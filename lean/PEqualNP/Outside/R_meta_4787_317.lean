import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 200000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.R_meta_4787_317
  (orbit :
  let U := Fin 13
  let S : Finset U := {0,1,3,9}
  let I := fun p l : U => ∃ d ∈ S, p = l+d
  let Rep (p l : U) := (p=0 ∧ l=12) ∨ (p=1 ∧ l=0) ∨ (p=1 ∧ l=1) ∨ (p=2 ∧ l=12) ∨ (p=2 ∧ l=2)
  ∀ (p l q m : U), I p l → I q m → ¬ (p=q ∧ l=m) →
      ∃ g h : U ≃ U, (∀ u v, I (g u) (h v) ↔ I u v) ∧ g p=0 ∧ h l=0 ∧ Rep (g q) (h m))
  (endpoint : let x1 : Type := Fin (13 : ℕ); have x2 : Finset x1 := {(0 : x1), (1 : x1), (3 : x1), (9 : x1)}; let x3 : x1 → x1 → Prop := fun (x3 x4 : x1) => ∃ x5 ∈ x2, x3 = x4 + x5; let x4 : Finset x1 → x1 → Prop := fun (x4 : Finset x1) (x5 : x1) => ∀ x6 ∈ x4, ¬x3 x6 x5; let x5 : Type := Fin (26 : ℕ) → Bool; have x6 : x1 → x1 → x5 := fun (x6 x7 : x1) (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x6 ∨ x8 = Fin.natAdd (13 : ℕ) x7); have x8 : Finset x1 → Prop := fun (x8 : Finset x1) => (∀ x9 ∉ x8, ∃ (x11 : x1), x4 x8 x11 ∧ x3 x9 x11) ∧ ((∃ (x9 : x1), ∀ x10 ∈ x8, x3 x10 x9) ∨ ∃ (x9 : x1), ∀ (x10 : x1), x4 x8 x10 → x3 x9 x10);
    ∀ C : Circuit, Monotone2 C → C.size ≤ 60 →
    let V : ℕ → x5 → Bool := fun i x => (C.wires (List.ofFn x ++ [true,false])).getD i false
    ∀ a b : ℕ, (∀ p l, x3 p l → (V a (x6 p l) || V b (x6 p l))=true) →
       (∀ P, x8 P → ∀ y : x5, (∀ z, y (Fin.castAdd 13 z)=true ↔ z∈P) →
         (∀ w, y (Fin.natAdd 13 w)=true ↔ x4 P w) → ¬(V a y || V b y)=true) → V a (x6 0 0)=false → (V b (x6 0 12) = false ∨ V b (x6 1 0) = false) → False)
  (crossing : let x1 : Type := Fin (13 : ℕ); have x2 : Finset x1 := {(0 : x1), (1 : x1), (3 : x1), (9 : x1)}; let x3 : x1 → x1 → Prop := fun (x3 x4 : x1) => ∃ x5 ∈ x2, x3 = x4 + x5; let x4 : Finset x1 → x1 → Prop := fun (x4 : Finset x1) (x5 : x1) => ∀ x6 ∈ x4, ¬x3 x6 x5; let x5 : Type := Fin (26 : ℕ) → Bool; have x6 : x1 → x1 → x5 := fun (x6 x7 : x1) (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x6 ∨ x8 = Fin.natAdd (13 : ℕ) x7); have x8 : Finset x1 → Prop := fun (x8 : Finset x1) => (∀ x9 ∉ x8, ∃ (x11 : x1), x4 x8 x11 ∧ x3 x9 x11) ∧ ((∃ (x9 : x1), ∀ x10 ∈ x8, x3 x10 x9) ∨ ∃ (x9 : x1), ∀ (x10 : x1), x4 x8 x10 → x3 x9 x10);
    ∀ C : Circuit, Monotone2 C → C.size ≤ 60 →
    let V : ℕ → x5 → Bool := fun i x => (C.wires (List.ofFn x ++ [true,false])).getD i false
    ∀ a b : ℕ, (∀ p l, x3 p l → (V a (x6 p l) || V b (x6 p l))=true) →
       (∀ P, x8 P → ∀ y : x5, (∀ z, y (Fin.castAdd 13 z)=true ↔ z∈P) →
         (∀ w, y (Fin.natAdd 13 w)=true ↔ x4 P w) → ¬(V a y || V b y)=true) → V a (x6 0 0)=false → (V b (x6 1 1) = false ∨ V b (x6 2 12) = false) → False)
  (opposite : let x1 : Type := Fin (13 : ℕ); have x2 : Finset x1 := {(0 : x1), (1 : x1), (3 : x1), (9 : x1)}; let x3 : x1 → x1 → Prop := fun (x3 x4 : x1) => ∃ x5 ∈ x2, x3 = x4 + x5; let x4 : Finset x1 → x1 → Prop := fun (x4 : Finset x1) (x5 : x1) => ∀ x6 ∈ x4, ¬x3 x6 x5; let x5 : Type := Fin (26 : ℕ) → Bool; have x6 : x1 → x1 → x5 := fun (x6 x7 : x1) (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x6 ∨ x8 = Fin.natAdd (13 : ℕ) x7); have x8 : Finset x1 → Prop := fun (x8 : Finset x1) => (∀ x9 ∉ x8, ∃ (x11 : x1), x4 x8 x11 ∧ x3 x9 x11) ∧ ((∃ (x9 : x1), ∀ x10 ∈ x8, x3 x10 x9) ∨ ∃ (x9 : x1), ∀ (x10 : x1), x4 x8 x10 → x3 x9 x10);
    ∀ C : Circuit, Monotone2 C → C.size ≤ 60 →
    let V : ℕ → x5 → Bool := fun i x => (C.wires (List.ofFn x ++ [true,false])).getD i false
    ∀ a b : ℕ, (∀ p l, x3 p l → (V a (x6 p l) || V b (x6 p l))=true) →
       (∀ P, x8 P → ∀ y : x5, (∀ z, y (Fin.castAdd 13 z)=true ↔ z∈P) →
         (∀ w, y (Fin.natAdd 13 w)=true ↔ x4 P w) → ¬(V a y || V b y)=true) → V a (x6 0 0)=false → V b (x6 2 2) = false → False)
  : let x1 : Type := Fin (13 : ℕ); have x2 : Finset x1 := {(0 : x1), (1 : x1), (3 : x1), (9 : x1)}; let x3 : x1 → x1 → Prop := fun (x3 x4 : x1) => ∃ x5 ∈ x2, x3 = x4 + x5; let x4 : Finset x1 → x1 → Prop := fun (x4 : Finset x1) (x5 : x1) => ∀ x6 ∈ x4, ¬x3 x6 x5; let x5 : Type := Fin (26 : ℕ) → Bool; have x6 : x1 → x1 → x5 := fun (x6 x7 : x1) (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x6 ∨ x8 = Fin.natAdd (13 : ℕ) x7); have x7 : Finset x1 → x5 := fun (x7 : Finset x1) (x8 : Fin (26 : ℕ)) => Decidable.decide ((∃ x9 ∈ x7, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ x4 x7 x9); have x8 : Finset x1 → Prop := fun (x8 : Finset x1) => (∀ x9 ∉ x8, ∃ (x11 : x1), x4 x8 x11 ∧ x3 x9 x11) ∧ ((∃ (x9 : x1), ∀ x10 ∈ x8, x3 x10 x9) ∨ ∃ (x9 : x1), ∀ (x10 : x1), x4 x8 x10 → x3 x9 x10); ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x9 →     x9.size ≤ (60 : ℕ) →       have x12 : ℕ → x5 → Bool := fun (x12 : ℕ) (x13 : x5) => (x9.wires (List.ofFn x13 ++ [Bool.true, Bool.false])).getD x12 Bool.false;       have x13 : (x5 → Bool) → Prop := fun (x13 : x5 → Bool) => ∀ (x14 x15 : x1), x3 x14 x15 → x13 (x6 x14 x15) = Bool.true;       ∀ (x14 x15 : ℕ), (x13 fun (x16 : x5) => x12 x14 x16 || x12 x15 x16) → ¬x13 (x12 x14) → ¬x13 (x12 x15) → (∀ (x19 : Finset x1), x8 x19 → ¬(x12 x14 (x7 x19) || x12 x15 (x7 x19)) = Bool.true) → False := by
  intro U S I A X T F N
  let Rep (p l : U) := (p=0 ∧ l=12) ∨ (p=1 ∧ l=0) ∨ (p=1 ∧ l=1) ∨ (p=2 ∧ l=12) ∨ (p=2 ∧ l=2)
  have normal (p l q m : U) (hpl : I p l) (hqm : I q m) (hd : ¬ (p=q ∧ l=m)) :
      ∃ g h : U ≃ U, (∀ u v, I (g u) (h v) ↔ I u v) ∧ g p=0 ∧ h l=0 ∧ Rep (g q) (h m) := by
    exact orbit p l q m hpl hqm hd
  intro C hC hsize V H a b hcov hna hnb hsafe
  change ¬ (∀ p l, I p l → V a (T p l)=true) at hna
  change ¬ (∀ p l, I p l → V b (T p l)=true) at hnb
  push Not at hna hnb
  obtain ⟨p,l,hi,hfa⟩ := hna
  obtain ⟨q,m,hj,hfb⟩ := hnb
  have fa : V a (T p l)=false := by cases e : V a (T p l) <;> first | rfl | exact (hfa e).elim | exact hfa
  have fb : V b (T q m)=false := by cases e : V b (T q m) <;> first | rfl | exact (hfb e).elim | exact hfb
  have distinct : ¬ (p=q ∧ l=m) := by
    rintro ⟨rfl,rfl⟩
    have c := hcov p l hi
    change (V a (T p l) || V b (T p l))=true at c
    rw [fa,fb] at c
    exact Bool.false_ne_true c
  obtain ⟨g,h,inc,hp,hl,hrep⟩ := normal p l q m hi hj distinct
  let perm : Fin 26 → Fin 26 :=
    Fin.addCases (m:=13) (n:=13) (motive:=fun _ => Fin 26)
      (fun v => Fin.castAdd 13 (g v)) (fun w => Fin.natAdd 13 (h w))
  let idx (i : ℕ) := if e : i<26 then (perm ⟨i,e⟩).val else i
  let rename (gate : Gate) : Gate := ⟨gate.op,gate.inputs.map idx⟩
  let D : Circuit := ⟨C.gates.map rename,idx C.output⟩
  have hd : Monotone2 D := by
    intro k hk
    obtain ⟨k',hk',rfl⟩ := List.mem_map.mp hk
    exact ⟨(hC k' hk').1,by simpa only [rename,List.length_map] using (hC k' hk').2⟩
  have hs : D.size ≤ 60 := by
    change (C.gates.map rename).length ≤ 60
    rw [List.length_map]
    exact hsize
  let W := fun (i : ℕ) (x : X) => (D.wires (List.ofFn x ++ [true,false])).getD i false
  have sim (x y : X) (xy : ∀ u, x u = y (perm u)) (i : ℕ) : V i x = W (idx i) y := by
    let step (z : List Bool) (k : Gate) := z ++ [k.op.eval (k.inputs.map fun u => z.getD u false)]
    have run (gs : List Gate) (u v : List Bool) (len : u.length=v.length) (h26 : 26 ≤ u.length)
        (agree : ∀ i, u.getD i false = v.getD (idx i) false) :
        ∀ i, (gs.foldl step u).getD i false = ((gs.map rename).foldl step v).getD (idx i) false := by
      induction gs generalizing u v with
      | nil => exact agree
      | cons k rest ih =>
        apply ih
        · simp [step,len]
        · simp [step]; omega
        · intro j
          have val : k.op.eval (k.inputs.map fun i => u.getD i false) =
              (rename k).op.eval ((rename k).inputs.map fun i => v.getD i false) := by
            congr 1
            simp only [rename,List.map_map]
            exact List.map_congr_left fun i _ => agree i
          by_cases hj : j < u.length
          · have hji : idx j < v.length := by
              dsimp [idx]
              split
              next e => exact lt_of_lt_of_le (perm ⟨j,e⟩).isLt (len ▸ h26)
              next _ => omega
            simpa only [step,List.getD_append _ _ _ _ hj,List.getD_append _ _ _ _ hji] using agree j
          · have same : idx j = j := dite_eq_right (by omega)
            simp only [step,same,val,List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hj),len,
              List.getD_append_right _ _ _ _ (show v.length ≤ j by omega)]
    apply run C.gates _ _ (by simp) (by simp)
    intro j
    by_cases hlt : j<26
    · have hi' := (perm ⟨j,hlt⟩).isLt
      have lx : j < (List.ofFn x).length := by simpa only [List.length_ofFn] using hlt
      have ly : (perm ⟨j,hlt⟩).val < (List.ofFn y).length := by simpa only [List.length_ofFn] using hi'
      rw [show idx j = (perm ⟨j,hlt⟩).val from dite_eq_left hlt,
        List.getD_append _ _ _ _ lx,List.getD_append _ _ _ _ ly]
      simpa only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left hlt,dite_eq_left hi',Option.getD_some]
        using xy ⟨j,hlt⟩
    · have ge : (List.ofFn x).length ≤ j := by simpa using Nat.le_of_not_gt hlt
      have ge' : (List.ofFn y).length ≤ j := by simpa using Nat.le_of_not_gt hlt
      simp only [idx,dite_eq_right hlt,List.getD_append_right _ _ _ _ ge,List.getD_append_right _ _ _ _ ge',List.length_ofFn]
  have diff (u v : U) : Fin.castAdd 13 u ≠ Fin.natAdd 13 v := by
    intro e
    have hh := congrArg Fin.val e
    have hu := u.isLt
    change u.val = 13+v.val at hh
    omega
  have eqp (u v : U) : Fin.castAdd 13 u = Fin.castAdd 13 v ↔ u=v := Fin.castAdd_inj
  have eql (u v : U) : Fin.natAdd 13 u = Fin.natAdd 13 v ↔ u=v := Fin.natAdd_inj 13
  have Tp (u v : U) (j : ℕ) : V j (T u v) = W (idx j) (T (g u) (h v)) := by
    apply sim
    intro k
    induction k using Fin.addCases (m:=13) (n:=13) with
    | left x =>
      simp only [T,perm,Fin.addCases_left,eqp,diff,or_false,g.injective.eq_iff]
    | right w =>
      simp only [T,perm,Fin.addCases_right,eql,Ne.symm (diff _ _),false_or,h.injective.eq_iff]
  have cv (u v : U) (hv : I u v) :
      (W (idx a) (T u v) || W (idx b) (T u v))=true := by
    obtain ⟨u,rfl⟩ := g.surjective u
    obtain ⟨v,rfl⟩ := h.surjective v
    rw [← Tp,← Tp]
    exact hcov u v ((inc u v).mp hv)
  have fp (R : Finset U) (u : U) : F R (Fin.castAdd 13 u) = true ↔ u∈R := by
    unfold F
    rw [decide_eq_true_eq]
    constructor
    · rintro (⟨z,hz,he⟩|⟨w,he,_⟩)
      · exact (eqp u z).mp he ▸ hz
      · exact (diff u w he).elim
    · intro hu; exact Or.inl ⟨u,hu,rfl⟩
  have fl (R : Finset U) (w : U) : F R (Fin.natAdd 13 w) = true ↔ A R w := by
    unfold F
    rw [decide_eq_true_eq]
    constructor
    · rintro (⟨z,_,he⟩|⟨v,he,ha⟩)
      · exact (diff z w he.symm).elim
      · exact (eql w v).mp he ▸ ha
    · intro hw; exact Or.inr ⟨w,rfl,hw⟩
  have neg (Q : Finset U) (hq : N Q) : ¬(W (idx a) (F Q) || W (idx b) (F Q))=true := by
    let P := Finset.univ.filter fun u : U => g u ∈ Q
    have mem (u : U) : u ∈ P ↔ g u ∈ Q := by simp [P]
    have miss (v : U) : A P v ↔ A Q (h v) := by
      constructor
      · intro hP z hz
        obtain ⟨u,rfl⟩ := g.surjective z
        exact fun hi => hP u ((mem u).mpr hz) ((inc u v).mp hi)
      · intro hQ u hu hi
        exact hQ (g u) ((mem u).mp hu) ((inc u v).mpr hi)
    have hn : N P := by
      obtain ⟨hcl,dl⟩ := hq
      refine ⟨?_,?_⟩
      · intro u hu
        obtain ⟨v,hw,he⟩ := hcl (g u) (fun h => hu ((mem u).mpr h))
        obtain ⟨w,rfl⟩ := h.surjective v
        exact ⟨w,(miss w).mpr hw,(inc u w).mp he⟩
      · rcases dl with ⟨v,hv⟩|⟨u,hu⟩
        · obtain ⟨w,rfl⟩ := h.surjective v
          exact Or.inl ⟨w,fun u h => (inc u w).mp (hv _ ((mem u).mp h))⟩
        · obtain ⟨z,rfl⟩ := g.surjective u
          exact Or.inr ⟨z,fun w h => (inc z w).mp (hu _ ((miss w).mp h))⟩
    have mapF (j : ℕ) : V j (F P) = W (idx j) (F Q) := by
      apply sim
      intro k
      induction k using Fin.addCases (m:=13) (n:=13) with
      | left u =>
        simp only [perm,Fin.addCases_left]
        exact Bool.eq_iff_iff.mpr ((fp P u).trans ((mem u).trans (fp Q (g u)).symm))
      | right w =>
        simp only [perm,Fin.addCases_right]
        exact Bool.eq_iff_iff.mpr ((fl P w).trans ((miss w).trans (fl Q (h w)).symm))
    rw [← mapF a,← mapF b]
    exact hsafe P hn
  have neg2 (Q : Finset U) (hq : N Q) (y : X)
      (yp : ∀ z : U, y (Fin.castAdd 13 z)=true ↔ z∈Q)
      (yl : ∀ w : U, y (Fin.natAdd 13 w)=true ↔ A Q w) :
      ¬ (W (idx a) y || W (idx b) y)=true := by
    have e : y=F Q := by
      funext k
      induction k using Fin.addCases (m:=13) (n:=13) with
      | left u => exact Bool.eq_iff_iff.mpr ((yp u).trans (fp Q u).symm)
      | right w => exact Bool.eq_iff_iff.mpr ((yl w).trans (fl Q w).symm)
    rw [e]
    exact neg Q hq
  rw [Tp,hp,hl] at fa
  rw [Tp] at fb
  rcases hrep with ⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩ <;> rw [h1,h2] at fb
  · exact endpoint D hd hs (idx a) (idx b) cv neg2 fa (Or.inl fb)
  · exact endpoint D hd hs (idx a) (idx b) cv neg2 fa (Or.inr fb)
  · exact crossing D hd hs (idx a) (idx b) cv neg2 fa (Or.inl fb)
  · exact crossing D hd hs (idx a) (idx b) cv neg2 fa (Or.inr fb)
  · exact opposite D hd hs (idx a) (idx b) cv neg2 fa fb
