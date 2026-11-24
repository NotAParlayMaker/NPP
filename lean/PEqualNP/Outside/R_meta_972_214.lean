import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The automorphisms below put the inputs of the first gate into three orbits.
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_972_214
    (sameSide :
      let F := fun (x : Fin 26 → Bool) => ∃ a b : Fin 26,
        (a.val / 13 ≠ b.val / 13 ∧ (a.val+b.val)%13 ∈ ([0,1,3,9] : List ℕ)) ∧
        x a = true ∧ x b = true;
      ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin 26 → Bool, D.eval (List.ofFn x ++ [x 0 || x 1]) = true ↔ F x) →
      63 ≤ D.size)
    (incidentOr :
      let F := fun (x : Fin 26 → Bool) => ∃ a b : Fin 26,
        (a.val / 13 ≠ b.val / 13 ∧ (a.val+b.val)%13 ∈ ([0,1,3,9] : List ℕ)) ∧
        x a = true ∧ x b = true;
      ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin 26 → Bool, D.eval (List.ofFn x ++ [x 0 || x 13]) = true ↔ F x) →
      63 ≤ D.size)
    (incidentAnd :
      let F := fun (x : Fin 26 → Bool) => ∃ a b : Fin 26,
        (a.val / 13 ≠ b.val / 13 ∧ (a.val+b.val)%13 ∈ ([0,1,3,9] : List ℕ)) ∧
        x a = true ∧ x b = true;
      ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin 26 → Bool, D.eval (List.ofFn x ++ [x 0 && x 13]) = true ↔ F x) →
      63 ≤ D.size)
    (nonincident :
      let F := fun (x : Fin 26 → Bool) => ∃ a b : Fin 26,
        (a.val / 13 ≠ b.val / 13 ∧ (a.val+b.val)%13 ∈ ([0,1,3,9] : List ℕ)) ∧
        x a = true ∧ x b = true;
      ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin 26 → Bool, D.eval (List.ofFn x ++ [x 0 || x 15]) = true ↔ F x) →
      63 ≤ D.size)
    : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26,
        (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25),
        (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24),
        (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24),
        (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22),
        (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20),
        (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24),
        (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → 64 ≤ C.size := by
  let adj (a b : Fin 26) : Prop :=
    a.val / 13 ≠ b.val / 13 ∧ (a.val+b.val)%13 ∈ ([0,1,3,9] : List ℕ)

  let target (x : Fin 26 → Bool) : Prop :=
    ∃ a b, adj a b ∧ x a = true ∧ x b = true

  -- Two stabilizers of input zero, a cyclic shift, and point-line duality.
  let gen : Fin 4 → Fin 26 → Fin 26 :=
    ![![0,12,1,2,7,4,6,5,3,8,11,10,9,14,13,17,16,18,19,24,21,23,22,20,25,15],
      ![0,10,1,6,2,8,7,12,3,11,4,5,9,16,13,17,22,18,24,23,15,19,14,20,21,25],
      ![12,0,1,2,3,4,5,6,7,8,9,10,11,14,15,16,17,18,19,20,21,22,23,24,25,13],
      ![13,14,15,16,17,18,19,20,21,22,23,24,25,0,1,2,3,4,5,6,7,8,9,10,11,12]]

  let act (w : List (Fin 4)) (i : Fin 26) : Fin 26 := w.foldl (fun v d => gen d v) i

  have gen_inj : ∀ (d : Fin 4) (i j : Fin 26), gen d i = gen d j → i = j := by
    dsimp only [gen, adj]
    decide +kernel
  have gen_adj : ∀ (d : Fin 4) (i j : Fin 26), adj (gen d i) (gen d j) ↔ adj i j := by
    dsimp only [gen, adj]
    decide +kernel

  have act_inj (w : List (Fin 4)) : Function.Injective (act w) := by
    induction w with
    | nil => exact fun _ _ h => h
    | cons d w ih => exact fun i j h => gen_inj d i j (ih h)

  have act_adj (w : List (Fin 4)) (a b : Fin 26) : adj (act w a) (act w b) ↔ adj a b := by
    induction w generalizing a b with
    | nil => rfl
    | cons d w ih => exact (ih (gen d a) (gen d b)).trans (gen_adj d a b)

  -- Move the first input to zero and use its stabilizer to move the second.
  let start (i : Fin 26) : List (Fin 4) :=
    (if i.val ≥ 13 then [3] else []) ++ List.replicate (i.val % 13) 2
  let fixRoot : Fin 26 → List (Fin 4) := ![[],[],[0],[0,0],[1,0],[0,1,0],[1,0,0,1,0],[0,0,1,0],[0,0,0],[0,0,0,0],[1,1,0],[1,0,1,0],[0,0,0,0,0],[],[0],[],[1,1,0],[0,1,0,0],[1,0,0],[0,0,0],[1],[0,0,1],[1,0],[0,1],[0,0],[0]]

  have root0 : ∀ i : Fin 26, act (start i) i = 0 := by
    dsimp only [act, start, gen]
    decide +kernel
  have fixes : ∀ i : Fin 26, i ≠ 0 → act (fixRoot i) 0 = 0 ∧
      (act (fixRoot i) i = 1 ∨ act (fixRoot i) i = 13 ∨ act (fixRoot i) i = 15) := by
    dsimp only [act, fixRoot, gen]
    decide +kernel

  have orbit (i j : Fin 26) (ne : i ≠ j) :
      ∃ π : Fin 26 ≃ Fin 26, π i = 0 ∧ (π j = 1 ∨ π j = 13 ∨ π j = 15) ∧
        ∀ a b, adj (π a) (π b) ↔ adj a b := by
    let w := start i
    let v := act w j
    have ri : act w i = 0 := root0 i
    have pos : v ≠ 0 := fun h => ne ((act_inj w) (ri.trans h.symm))
    let term := fixRoot v
    let f := act term ∘ act w
    have inj : Function.Injective f := (act_inj term).comp (act_inj w)
    let π := Equiv.ofBijective f ((Finite.injective_iff_bijective).mp inj)
    refine ⟨π,?_,(fixes v pos).2,?_⟩
    · change act term (act w i) = 0
      rw [ri]
      exact (fixes v pos).1
    · intro a b
      exact (act_adj term _ _).trans (act_adj w _ _)

  have getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
    simp

  -- Relabel raw inputs and translate every later wire by the change in arity.
  let wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
    if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

  let relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
    ⟨g.op, g.inputs.map (wmap n m π)⟩

  let relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
    ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  let Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
    n ≤ W.length ∧ W'.length + n = W.length + m ∧
      ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

  have rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
      (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
    obtain ⟨h1, h2, h3⟩ := h
    have hv : (relGate n m π g).op.eval
        ((relGate n m π g).inputs.map fun i => W'.getD i false)
        = g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [relGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact h3 a
    refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
    intro w
    simp only [step, hv]
    rcases Nat.lt_trichotomy w W.length with hw | hw | hw
    · have hlt : wmap n m π w < W'.length := by
        dsimp only [wmap]
        split
        · have := (π ⟨w, by assumption⟩).2; omega
        · omega
      rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
      exact h3 w
    · have he : wmap n m π w = W'.length := by
        dsimp only [wmap]
        split
        · omega
        · omega
      rw [he, hw, getD_snoc_eq, getD_snoc_eq]
    · have hge : W'.length + 1 ≤ wmap n m π w := by
        dsimp only [wmap]
        split
        · omega
        · omega
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

  have rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
      ∀ W W' : List Bool, Rel n m π W W' →
        Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
    induction gs with
    | nil => intro W W' h; exact h
    | cons g gs ih =>
      intro W W' h
      exact ih _ _ (rel_step n m π W W' g h)

  have rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
      Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
    refine ⟨by simp, by simp; omega, ?_⟩
    intro w
    dsimp only [wmap]
    split
    · rename_i hw
      rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
      simp
    · rename_i hw
      rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

  -- Missing input wires read as false, including any forward reference.
  have first_form (g : Gate)
      (allowed : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
      ∃ i j : Fin 26, i ≠ j ∧ ∃ f : Bool × Bool → Bool, Monotone f ∧ ∀ x : Fin 26 → Bool,
        g.op.eval (g.inputs.map (fun k => (List.ofFn x).getD k false)) = f (x i, x j) := by
    classical
    let used := (g.inputs.map (Fin.ofNat 26)).toFinset
    have small : used.card ≤ 2 := by
      exact (List.toFinset_card_le _).trans (by simpa using allowed.2)
    obtain ⟨u,sub,_,sz⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ used) small (by simp)
    obtain ⟨i,j,ne,rfl⟩ := Finset.card_eq_two.mp sz
    let read (z : Bool × Bool) (k : ℕ) := if 26 ≤ k then false else if k = i.val then z.1 else z.2
    let f (z : Bool × Bool) := g.op.eval (g.inputs.map (read z))
    refine ⟨i,j,ne,f,?_,?_⟩
    · intro a b hab
      have step (k : ℕ) : read a k ≤ read b k := by
        dsimp only [read]
        split
        · rfl
        · split
          · exact hab.1
          · exact hab.2
      apply Bool.le_iff_imp.mpr
      rcases allowed.1 with ho | ho
      · change g.op = .and at ho
        simp only [f,ho]
        change List.all _ _ = true → List.all _ _ = true
        simp only [List.all_eq_true,List.mem_map,id_eq]
        rintro yes v ⟨k,hk,rfl⟩
        exact (Bool.le_iff_imp.mp (step k)) (yes _ ⟨k,hk,rfl⟩)
      · change g.op = .or at ho
        simp only [f,ho]
        change List.any _ _ = true → List.any _ _ = true
        simp only [List.any_eq_true,List.mem_map,id_eq]
        rintro ⟨v,⟨k,hk,rfl⟩,hot⟩
        exact ⟨_,⟨k,hk,rfl⟩,Bool.le_iff_imp.mp (step k) hot⟩
    · intro x
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro k hk
      by_cases lt : k < 26
      · have inside : Fin.ofNat 26 k ∈ used := List.mem_toFinset.mpr (List.mem_map.mpr ⟨k,hk,rfl⟩)
        have cases := sub inside
        simp only [Finset.mem_insert,Finset.mem_singleton] at cases
        have cast : Fin.ofNat 26 k = ⟨k,lt⟩ := Fin.ext (Nat.mod_eq_of_lt lt)
        rw [cast] at cases
        rw [List.getD_eq_getElem _ _ (by simpa using lt), List.getElem_ofFn]
        rcases cases with e | e
        · have v := congrArg Fin.val e
          simp only at v
          simp [read,v]
        · have v := congrArg Fin.val e
          have ni : k ≠ i.val := fun h => ne (Fin.ext (h.symm.trans v))
          simp [read,lt.not_ge,ni,e]
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt lt)]
        simp [read,Nat.le_of_not_lt lt]

  have orient (g : Gate)
      (allowed : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
      ∃ i j : Fin 26, i ≠ j ∧ ∃ f : Bool × Bool → Bool, Monotone f ∧
        f (false,true) ≤ f (true,false) ∧ ∀ x : Fin 26 → Bool,
        g.op.eval (g.inputs.map (fun k => (List.ofFn x).getD k false)) = f (x i,x j) := by
    obtain ⟨i,j,ne,f,m,h⟩ := first_form g allowed
    rcases le_total (f (false,true)) (f (true,false)) with yes | no
    · exact ⟨i,j,ne,f,m,yes,h⟩
    · exact ⟨j,i,ne.symm,fun z => f (z.2,z.1),fun _ _ le => m ⟨le.2,le.1⟩,no,h⟩

  have classify (f : Bool × Bool → Bool) (m : Monotone f)
      (orient : f (false,true) ≤ f (true,false)) :
      f = (fun z => z.1 || z.2) ∨ f = (fun z => z.1 && z.2) ∨
      ∀ a b c, f (a,b) = f (a,c) := by
    have h0 : f (false,false) ≤ f (false,true) := m (by decide : (false,false) ≤ (false,true))
    have h1 : f (true,false) ≤ f (true,true) := m (by decide : (true,false) ≤ (true,true))
    have values (p q r s : Bool) (a : p ≤ q) (b : q ≤ r) (c : r ≤ s) :
        (p=false ∧ q=true ∧ r=true ∧ s=true) ∨ (p=false ∧ q=false ∧ r=false ∧ s=true) ∨
        (p=q ∧ r=s) := by revert p q r s; decide
    rcases values _ _ _ _ h0 orient h1 with h | h | h
    · left
      funext z
      have both (a b : Bool) : f (a,b) = (a || b) := by
        cases a <;> cases b <;> simp [h.1,h.2.1,h.2.2.1,h.2.2.2]
      exact both z.1 z.2
    · right; left
      funext z
      have both (a b : Bool) : f (a,b) = (a && b) := by
        cases a <;> cases b <;> simp [h.1,h.2.1,h.2.2.1,h.2.2.2]
      exact both z.1 z.2
    · right
      right
      intro a b c
      cases a <;> cases b <;> cases c <;> simp [h.1,h.2]

  have normalize (C : Circuit) (hm : Monotone2 C)
      (val : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ target x) :
      ∃ k : Fin 26, (k=1 ∨ k=13 ∨ k=15) ∧ ∃ (D : Circuit) (f : Bool × Bool → Bool),
        Monotone2 D ∧ Monotone f ∧ f (false,true) ≤ f (true,false) ∧ D.size < C.size ∧ ∀ x : Fin 26 → Bool,
        D.eval (List.ofFn x ++ [f (x 0,x k)]) = true ↔ target x := by
    cases e : C.gates with
    | nil =>
      exfalso
      have hit : target (fun _ => true) := ⟨0,13,by dsimp only [adj]; decide,rfl,rfl⟩
      have yes := (val _).mpr hit
      change (C.gates.foldl _ (List.ofFn (fun _ : Fin 26 => true))).getD C.output false = true at yes
      rw [e,List.foldl_nil] at yes
      have bound : C.output < 26 := by
        by_contra! h
        rw [List.getD_eq_default _ _ (by simpa using h)] at yes
        contradiction
      let i : Fin 26 := ⟨C.output,bound⟩
      let z := fun a : Fin 26 => decide (a=i)
      have out : C.eval (List.ofFn z) = true := by
        change (C.gates.foldl _ (List.ofFn z)).getD C.output false = true
        rw [e,List.foldl_nil,List.getD_eq_getElem _ _ (by simpa using bound),List.getElem_ofFn]
        exact decide_eq_true rfl
      obtain ⟨a,b,inc,za,zb⟩ := (val z).mp out
      have aa : a = i := of_decide_eq_true za
      have bb : b = i := of_decide_eq_true zb
      exact inc.1 (by rw [aa,bb])
    | cons g gs =>
      obtain ⟨i,j,ne,f,mono,order,first⟩ := orient g (hm g (by simp [e]))
      obtain ⟨π,ri,kind,auto⟩ := orbit i j ne
      let D := relabel 26 26 π (⟨gs,C.output⟩ : Circuit)
      refine ⟨π j,kind,D,f,?_,mono,order,?_,?_⟩
      · intro d hd
        obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hd
        have h := hm u (e ▸ List.mem_cons_of_mem g hu)
        exact ⟨h.1,by simpa [relGate] using h.2⟩
      · change (gs.map _).length < C.gates.length
        simp [e]
      · intro x
        let z := x ∘ π
        let b := f (x 0,x (π j))
        have rel : Rel 26 26 π (List.ofFn z ++ [b]) (List.ofFn x ++ [b]) := by
          refine ⟨by simp,by simp,?_⟩
          intro n
          by_cases hn : n<26
          · have lk : wmap 26 26 π n < 26 := by simp [wmap,hn]
            rw [List.getD_append _ _ _ _ (by simpa using lk),List.getD_append _ _ _ _ (by simpa using hn)]
            exact (rel_init 26 26 π x).2.2 n
          · have mapn : wmap 26 26 π n = n := by simp [wmap,hn]; omega
            rw [mapn,List.getD_append_right _ _ _ _ (by simp; omega),List.getD_append_right _ _ _ _ (by simp; omega)]
            simp
        have fold := (rel_fold 26 26 π gs _ _ rel).2.2 C.output
        have bit := first z
        change _ = f (x (π i),x (π j)) at bit
        rw [ri] at bit
        have same : D.eval (List.ofFn x ++ [b]) = C.eval (List.ofFn z) := by
          change _ = (C.gates.foldl step (List.ofFn z)).getD C.output false
          rw [e,List.foldl_cons]
          change _ = (gs.foldl step (List.ofFn z ++ [g.op.eval _])).getD C.output false
          rw [bit]
          exact fold
        change D.eval (List.ofFn x ++ [b]) = true ↔ target x
        rw [same,val]
        constructor
        · rintro ⟨a,b,edge,u,v⟩
          exact ⟨π a,π b,(auto a b).mpr edge,u,v⟩
        · rintro ⟨a,b,edge,u,v⟩
          obtain ⟨aa,rfl⟩ := π.surjective a
          obtain ⟨bb,rfl⟩ := π.surjective b
          exact ⟨aa,bb,(auto aa bb).mp edge,u,v⟩
  let wiresFrom := fun (gs : List Gate) (w : List Bool) => gs.foldl step w
  have gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
      (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
      (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
      op.eval l₁ = true → op.eval l₂ = true := by
    rcases hop with rfl | rfl
    · change l₁.all id = true → l₂.all id = true
      simp only [List.all_eq_true, id_eq]
      intro h b hb
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
      have h1 : l₁.getD i false = true := by
        have hi1 : i < l₁.length := by omega
        rw [List.getD_eq_getElem _ _ hi1]
        exact h _ (List.getElem_mem hi1)
      have h2 := hle i h1
      rwa [List.getD_eq_getElem _ _ hi] at h2
    · change l₁.any id = true → l₂.any id = true
      simp only [List.any_eq_true,id_eq]
      rintro ⟨b, hb, rfl⟩
      obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
      have h1 : l₁.getD i false = true := by
        rw [List.getD_eq_getElem _ _ hi]; exact hbi
      have h2 := hle i h1
      have hi2 : i < l₂.length := by omega
      rw [List.getD_eq_getElem _ _ hi2] at h2
      exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

  have wiresFrom_mono (gs : List Gate)
      (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
      ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
        (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
        ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
    induction gs with
    | nil =>
      intro w₁ w₂ _ hle i hi
      exact hle i hi
    | cons g gs ih =>
      intro w₁ w₂ hlen hle i hi
      have hstep1 : wiresFrom (g :: gs) w₁ =
          wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
      have hstep2 : wiresFrom (g :: gs) w₂ =
          wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
      rw [hstep1] at hi
      rw [hstep2]
      apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
      intro j hj
      by_cases hlt : j < w₁.length
      · rw [List.getD_append _ _ _ _ hlt] at hj
        rw [List.getD_append _ _ _ _ (by omega)]
        exact hle j hj
      · by_cases heq : j = w₁.length
        · subst heq
          rw [getD_snoc_eq] at hj
          rw [hlen, getD_snoc_eq]
          exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
            (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
            (by simp) (by
              intro t ht
              by_cases ht_lt : t < g.inputs.length
              · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
                rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
                simp only [List.getElem_map] at ht ⊢
                exact hle _ ht
              · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
                exact Bool.noConfusion ht) hj
        · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
          exact Bool.noConfusion hj
  have eval_up (D : Circuit) (md : Monotone2 D) (x y : Fin 26 → Bool) (b c : Bool)
      (xy : ∀ a, x a = true → y a = true) (bc : b = true → c = true) :
      D.eval (List.ofFn x ++ [b]) = true → D.eval (List.ofFn y ++ [c]) = true := by
    apply wiresFrom_mono D.gates (fun g h => (md g h).1) _ _ (by simp) _ D.output
    intro n
    by_cases hn : n < 26
    · rw [List.getD_append _ _ _ _ (by simpa using hn), List.getD_append _ _ _ _ (by simpa using hn)]
      rw [List.getD_eq_getElem _ _ (by simpa using hn), List.getD_eq_getElem _ _ (by simpa using hn)]
      simpa only [List.getElem_ofFn] using xy ⟨n,hn⟩
    · rw [List.getD_append_right _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp; omega)]
      by_cases en : n=26
      · subst n
        simpa using bc
      · have nz : n-26 ≠ 0 := by omega
        simp [nz]
  -- An AND on a nonedge vanishes on every minimal positive input.
  have clamp (k : Fin 26) (miss : ¬ adj 0 k) (rev : ¬ adj k 0) (ne : 0 ≠ k)
      (D : Circuit) (md : Monotone2 D)
      (tail : ∀ x : Fin 26 → Bool, D.eval (List.ofFn x ++ [x 0 && x k]) = true ↔ target x) :
      ∀ x : Fin 26 → Bool, D.eval (List.ofFn x ++ [false]) = true ↔ target x := by
    intro x
    constructor
    · exact fun h => (tail x).mp (eval_up D md x x false _ (fun _ h => h) (by simp) h)
    · rintro ⟨u,v,edge,hu,hv⟩
      let z (a : Fin 26) := decide (a=u ∨ a=v)
      have low (a : Fin 26) (h : z a = true) : x a = true := by
        rcases of_decide_eq_true h with rfl | rfl <;> assumption
      have off : (z 0 && z k) = false := by
        apply Bool.eq_false_iff.mpr
        intro h
        obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp h
        rcases of_decide_eq_true a with a | a <;> rcases of_decide_eq_true b with b | b
        · exact ne (a.trans b.symm)
        · exact miss (a ▸ b ▸ edge)
        · exact rev (a ▸ b ▸ edge)
        · exact ne (a.trans b.symm)
      have hit : target z := ⟨u,v,edge,by simp [z],by simp [z]⟩
      have yes := (tail z).mpr hit
      rw [off] at yes
      exact eval_up D md z x false false low id yes

  -- Substitute a fixed bit or the first input for wire twenty-six in the tail.
  have unaryTail (D : Circuit) (md : Monotone2 D) (f : Bool → Bool) (mf : Monotone f)
      (tail : ∀ x : Fin 26 → Bool, D.eval (List.ofFn x ++ [f (x 0)]) = true ↔ target x) :
      ∃ E : Circuit, Monotone2 E ∧ E.size = D.size ∧ ∀ x : Fin 26 → Bool,
        E.eval (List.ofFn x ++ [x 0 || x 13]) = true ↔ target x := by
    classical
    let copy := f false != f true
    let c := f false
    have form (b : Bool) : f b = if copy then b else c := by
      have le : f false ≤ f true := mf (by decide)
      cases b <;> cases l : f false <;> cases r : f true <;> simp [copy,c,l,r] at le ⊢ <;> exact (by decide : ¬ true ≤ false) le
    let pin (a : ℕ) := if a=26 then 0 else a
    let absorb : GateOp := if c then .or else .and
    let rewriteGate (g : Gate) : Gate :=
      if copy then ⟨g.op,g.inputs.map pin⟩
      else if g.op = absorb ∧ 26 ∈ g.inputs then ⟨if c then .and else .or,[]⟩
      else ⟨g.op,g.inputs.filter (· != 26)⟩
    have allowed (g : Gate) (h : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
        (rewriteGate g).op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ (rewriteGate g).inputs.length ≤ 2 := by
      dsimp only [rewriteGate]; split
      · simpa using h
      · split
        · cases c <;> simp
        · exact ⟨h.1,(List.length_filter_le _ _).trans h.2⟩
    let agree (w v : List Bool) := 26 < w.length ∧ w.length = v.length ∧
      w.getD 26 false = f (v.getD 0 false) ∧ ∀ i, i ≠ 26 → w.getD i false = v.getD i false
    have andE (l : List Bool) : GateOp.and.eval l = l.all id := rfl
    have orE (l : List Bool) : GateOp.or.eval l = l.any id := rfl
    have eqBit (g : Gate) (allowed : g.op = .and ∨ g.op = .or)
        (w v : List Bool) (ag : agree w v) :
        g.op.eval (g.inputs.map fun i => w.getD i false) =
        (rewriteGate g).op.eval ((rewriteGate g).inputs.map fun i => v.getD i false) := by
      by_cases cpy : copy = true
      · simp only [rewriteGate,cpy,ite_true,List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases e : i=26
        · subst i
          simpa [pin,form,cpy] using ag.2.2.1
        · simpa [pin,e] using ag.2.2.2 i e
      · have atPin : w.getD 26 false = c := by simpa [form,cpy] using ag.2.2.1
        have atOther := ag.2.2.2
        have mapped : (g.inputs.filter (· != 26)).map (fun i => w.getD i false) =
            (g.inputs.filter (· != 26)).map (fun i => v.getD i false) := by
          apply List.map_congr_left
          intro i hi
          exact atOther _ (by simpa using (List.mem_filter.mp hi).2)
        by_cases mem : 26 ∈ g.inputs
        · rcases allowed with ho | ho
          · cases ec : c
            · have off : (g.inputs.map fun i => w.getD i false).all id = false := by
                apply Bool.eq_false_iff.mpr
                intro h
                have on := List.all_eq_true.mp h _ (List.mem_map_of_mem (f := fun i => w.getD i false) mem)
                change w.getD 26 false = true at on
                rw [atPin,ec] at on
                contradiction
              simpa only [rewriteGate,cpy,↓reduceIte,absorb,ec,Bool.false_eq_true,ite_false,ite_true,ho,mem,and_self,orE,List.map_nil,List.any_nil,andE] using off
            · simp only [rewriteGate,cpy,↓reduceIte,absorb,ec,ho,reduceCtorEq,false_and,
                andE,← mapped,List.all_map,List.all_filter]
              apply List.all_congr rfl
              intro i
              by_cases e : i=26 <;> simp [e]
              simpa only [List.getD_eq_getElem?_getD] using atPin.trans ec
          · cases ec : c
            · simp only [rewriteGate,cpy,↓reduceIte,absorb,ec,ho,reduceCtorEq,false_and,
                orE,← mapped,List.any_map,List.any_filter]
              apply List.any_congr rfl
              intro i
              by_cases e : i=26 <;> simp [e]
              simpa only [List.getD_eq_getElem?_getD] using atPin.trans ec
            · have on : (g.inputs.map fun i => w.getD i false).any id = true :=
                List.any_eq_true.mpr ⟨_,List.mem_map_of_mem mem,atPin.trans ec⟩
              simpa only [rewriteGate,cpy,↓reduceIte,Bool.false_eq_true,ite_false,absorb,ec,ite_true,ho,mem,and_self,andE,List.map_nil,List.all_nil,orE] using on
        · have no : g.inputs.filter (· != 26) = g.inputs := List.filter_eq_self.mpr (by
            intro a ha
            exact bne_iff_ne.mpr (fun e => mem (e ▸ ha)))
          simp only [rewriteGate,cpy,↓reduceIte,Bool.false_eq_true,mem,and_false]
          rw [← mapped,no]
    have advance (g : Gate) (hg : g.op = .and ∨ g.op = .or) (w v : List Bool) (ag : agree w v) :
        agree (step w g) (step v (rewriteGate g)) := by
      obtain ⟨bound,len,read,same⟩ := ag
      have value := eqBit g hg w v ⟨bound,len,read,same⟩
      dsimp only [step,agree]
      refine ⟨by simp; omega,by simp [len],?_,?_⟩
      · rw [List.getD_append _ _ _ _ bound,List.getD_append _ _ _ _ (by omega)]
        exact read
      · intro i diff
        by_cases lt : i < w.length
        · rw [List.getD_append _ _ _ _ lt,List.getD_append _ _ _ _ (by omega)]
          exact same i diff
        · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),len,value]
    have folds (gs : List Gate) (h : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
        (w v : List Bool) (ag : agree w v) :
        agree (gs.foldl step w) ((gs.map rewriteGate).foldl step v) := by
      induction gs generalizing w v with
      | nil => exact ag
      | cons g gs ih =>
        exact ih (fun a ha => h a (List.mem_cons_of_mem _ ha)) _ _
          (advance g (h g List.mem_cons_self) w v ag)
    let E : Circuit := ⟨D.gates.map rewriteGate,D.output⟩
    have state (x : Fin 26 → Bool) : agree (D.wires (List.ofFn x ++ [f (x 0)]))
        (E.wires (List.ofFn x ++ [x 0 || x 13])) := by
      apply folds _ (fun g hg => (md g hg).1)
      refine ⟨by simp,by simp,?_,?_⟩
      · simp [List.getD_eq_getElem?_getD]
      · intro i ne
        by_cases lt : i<26
        · rw [List.getD_append _ _ _ _ (by simpa using lt),List.getD_append _ _ _ _ (by simpa using lt)]
        · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
    have keep (gs : List Gate) (w : List Bool) (i : ℕ) (lt : i<w.length) :
        (gs.foldl step w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons,ih _ (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ lt
    have out : D.output ≠ 26 := by
      intro bad
      have raw (x : Fin 26 → Bool) : D.eval (List.ofFn x ++ [f (x 0)]) = f (x 0) := by
        change (D.gates.foldl step _).getD D.output false = _
        rw [bad,keep _ _ _ (by simp)]
        simp [List.getD_eq_getElem?_getD]
      let z := fun i : Fin 26 => decide (i=1 ∨ i=13)
      have yes := (tail z).mpr ⟨1,13,by dsimp only [adj]; decide,by simp [z],by simp [z]⟩
      have off : z 0 = false := by dsimp only [z]; decide
      rw [raw,off] at yes
      have no := (tail (fun _ => false)).mp ((raw _).trans yes)
      obtain ⟨_,_,_,bad,_⟩ := no
      contradiction
    refine ⟨E,?_,by change (D.gates.map rewriteGate).length = D.gates.length; simp,?_⟩
    · intro g hg
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
      exact allowed a (md a ha)
    · intro x
      exact Iff.trans (Iff.of_eq (congrArg (· = true) ((state x).2.2.2 D.output out).symm)) (tail x)

  let edges : List (ℕ × ℕ) := [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25),
        (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24),
        (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24),
        (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22),
        (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20),
        (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24),
        (12, 14), (12, 15), (12, 17), (12, 23)]
  have table : ∀ a b : Fin 26, ((a.val,b.val) ∈ edges ∨ (b.val,a.val) ∈ edges) ↔ adj a b := by
    dsimp only [edges,adj]
    decide +kernel
  intro C hm hv
  have val (x : Fin 26 → Bool) : C.eval (List.ofFn x) = true ↔ target x := by
    constructor
    · intro h
      obtain ⟨a,b,edge,ha,hb⟩ := (hv x).mp h
      exact ⟨a,b,(table a b).mp (Or.inl edge),ha,hb⟩
    · rintro ⟨a,b,edge,ha,hb⟩
      apply (hv x).mpr
      rcases (table a b).mpr edge with l | r
      · exact ⟨a,b,l,ha,hb⟩
      · exact ⟨b,a,r,hb,ha⟩
  obtain ⟨k,kind,D,f,md,mf,order,short,tail⟩ := normalize C hm val
  have bound : 63 ≤ D.size := by
    rcases classify f mf order with rfl | rfl | one
    · rcases kind with rfl | rfl | rfl
      · exact sameSide D md tail
      · exact incidentOr D md tail
      · exact nonincident D md tail
    · by_cases e : k=13
      · subst k
        exact incidentAnd D md tail
      · have other : k=1 ∨ k=15 := by tauto
        have facts : (¬ adj 0 k) ∧ (¬ adj k 0) ∧ 0 ≠ k := by
          rcases other with rfl | rfl <;> dsimp only [adj] <;> decide
        obtain ⟨E,me,sz,h⟩ := unaryTail D md (fun _ => false) (fun _ _ _ => le_rfl)
          (clamp k facts.1 facts.2.1 facts.2.2 D md tail)
        exact sz ▸ incidentOr E me h
    · obtain ⟨E,me,sz,h⟩ := unaryTail D md (fun a => f (a,false)) (fun _ _ le => mf ⟨le,le_rfl⟩) (by
        intro x
        simpa only [one (x 0) false (x k)] using tail x)
      exact sz ▸ incidentOr E me h
  omega
