import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The 24 boundary rows, negative-mask argument and cycle rotations are adapted
-- from heehii2's PR #9715. Gan-Tu's PR #8967 also uses private reader masks.
-- All gates keep their chronological order here. Every result must improve on
-- each earlier wire on an edge or a maximal independent set, and on constant false.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_4223_73
    (separates :
      let A : List (BitVec 24) := [5521457,8532035,3227782,430348,11083800,113184,902208,13501056,15731968]
      let E : List (Fin 9 × Fin 9) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
      ∀ C : Circuit, IsMinimalCircuit 9 C →
        (∀ g ∈ C.gates, g.op = .and ∨ g.op = .or) →
        (circuitFun 9 C = fun x => E.any fun e => x e.1 && x e.2) →
        let V (r : Fin 24) (w : ℕ) :=
          (C.wires (List.ofFn fun v : Fin 9 => (A.getD v.val 0).getLsbD r.val)).getD w false
        ∀ (j : Fin C.size) (b : ℕ), (b < 9+j.val ∨ b = 9+C.size) →
          ∃ r : Fin 24, V r (9+j.val) ≠ V r b ∧ V r (9+j.val) = decide (r.val < 12))
    (exclude :
      let A : List (BitVec 24) := [5521457,8532035,3227782,430348,11083800,113184,902208,13501056,15731968]
      let tags : List ℕ := [4,6,7]
      ∀ (n : ℕ), n ≤ 15 → ∀ (w : Fin (9+n) → BitVec 24) (a b : Fin n → ℕ) (op : Fin n → Bool),
        let v (i : ℕ) := (List.ofFn w).getD i 0
        let read (s : ℕ) (j : Fin n) := a j = s ∨ b j = s
        let wins (x y : BitVec 24) := ∃ r : Fin 24,
          x.getLsbD r.val ≠ y.getLsbD r.val ∧ x.getLsbD r.val = decide (r.val < 12)
        (∀ i : Fin 9, v i.val = A.getD i.val 0) →
        v 9 ∈ ([1,14053491,7684279,5689661] : List (BitVec 24)) →
        (∀ j : Fin n, a j < 9+j.val ∧ b j < 9+j.val ∧ a j ≠ b j ∧
          v (9+j.val) = if op j then v (a j) ||| v (b j) else v (a j) &&& v (b j)) →
        (∀ s ∈ tags, ∃ j : Fin n, (∀ k, read s k ↔ k=j) ∧ op j = true ∧
          v (9+j.val) &&& 16773120 = v s &&& 16773120) →
        (∀ j : Fin n, a j ∈ tags → b j ∈ tags → a j = b j) →
        (∀ (j : Fin n) (i : ℕ), (i < 9+j.val ∨ i = 9+n) → wins (v (9+j.val)) (v i)) →
        ∀ j : Fin n, v (9+j.val) ≠ 4095)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x1 → x1.size ≤ (15 : ℕ) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (∀ (x5 : Fin x1.size), (∀ x6 ∈ (x1.gates.get x5).inputs, x6 < (9 : ℕ) + ↑x5) ∧ (x1.gates.get x5).inputs.Nodup ∧ ((x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x5).inputs.length = (1 : ℕ) ∨ (x1.gates.get x5).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x5).inputs.length = (2 : ℕ))) → (∀ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], ∃ (x8 : Fin x1.size), (∀ (x9 : Fin x1.size), ↑x6 ∈ (x1.gates.get x9).inputs ↔ x9 = x8) ∧ (x1.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ (x7 : Fin x1.size), ∀ x8 ∈ (x1.gates.get x7).inputs, ∀ x10 ∈ (x1.gates.get x7).inputs, x8 ∈ [(4 : ℕ), (6 : ℕ), (7 : ℕ)] → x10 ∈ [(4 : ℕ), (6 : ℕ), (7 : ℕ)] → x8 = x10) → (∀ (x8 : Fin x1.size), (x1.gates.get x8).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → False := by
  classical
  intro C minimal small computes wiring unique separated noNot
  let E : List (Fin 9 × Fin 9) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
  let graph (x : Fin 9 → Bool) := E.any fun e => x e.1 && x e.2
  let sel (s : Fin 3) : Fin 9 := if s = 0 then 4 else if s = 1 then 6 else 7
  let A : List (BitVec 24) := [5521457,8532035,3227782,430348,11083800,113184,902208,13501056,15731968]
  let H : List (BitVec 24) := [5521457,8532035,3227782,430348,113184,15731968]
  let M : List (BitVec 24) := [11083800,902208,13501056]
  let X (r : Fin 24) (v : Fin 9) := (A.getD v.val 0).getLsbD r.val
  let V (x : Fin 9 → Bool) (w : ℕ) := (C.wires (List.ofFn x)).getD w false
  let gt (j : Fin C.size) := C.gates.get j
  have inp (x : Fin 9 → Bool) (v : Fin 9) : V x v.val = x v := by
    let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have ext (gs : List Gate) (xs : List Bool) : ∃ tail, gs.foldl step xs = xs ++ tail := by
      induction gs generalizing xs with
      | nil => exact ⟨[], by simp⟩
      | cons g gs ih =>
        obtain ⟨t, ht⟩ := ih (step xs g)
        exact ⟨[_] ++ t, by simpa [List.foldl_cons, step, List.append_assoc] using ht⟩
    obtain ⟨t, ht⟩ := ext C.gates (List.ofFn x)
    change (C.gates.foldl step (List.ofFn x)).getD v.val false = x v
    rw [ht, List.getD_append _ _ _ _ (by simpa using v.isLt),
      List.getD_eq_getElem _ _ (by simpa using v.isLt), List.getElem_ofFn]
  have equation (j : Fin C.size) (x : Fin 9 → Bool) :
      V x (9 + j.val) = (gt j).op.eval ((gt j).inputs.map (V x)) := by
    let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let pref (k : ℕ) := (C.gates.take k).foldl step (List.ofFn x)
    have sizeFold (gs : List Gate) (xs : List Bool) : (gs.foldl step xs).length = xs.length + gs.length := by
      induction gs generalizing xs with
      | nil => simp
      | cons g gs ih => rw [List.foldl_cons, ih]; simp [step]; omega
    have sizePref (k : ℕ) (hk : k ≤ C.size) : (pref k).length = 9 + k := by
      unfold pref
      rw [sizeFold,List.length_ofFn,List.length_take_of_le hk]
    have ext (gs : List Gate) (xs : List Bool) : ∃ tail, gs.foldl step xs = xs ++ tail := by
      induction gs generalizing xs with
      | nil => exact ⟨[], by simp⟩
      | cons g gs ih =>
        obtain ⟨t, ht⟩ := ih (step xs g)
        exact ⟨[_] ++ t, by simpa [List.foldl_cons, step, List.append_assoc] using ht⟩
    have stable (k w : ℕ) (hk : k ≤ C.size) (hw : w < 9+k) : V x w = (pref k).getD w false := by
      obtain ⟨t, ht⟩ := ext (C.gates.drop k) (pref k)
      change (C.gates.foldl step (List.ofFn x)).getD w false = _
      conv_lhs => rw [← List.take_append_drop k C.gates, List.foldl_append]
      rw [show (C.gates.drop k).foldl step ((C.gates.take k).foldl step (List.ofFn x)) = pref k ++ t from ht]
      exact List.getD_append _ _ _ _ (by rwa [sizePref k hk])
    have hn : j.val < C.gates.length := j.isLt
    have next : pref (j.val+1) = step (pref j.val) (gt j) := by
      unfold pref
      rw [List.take_succ_eq_append_getElem hn, List.foldl_append]
      rfl
    rw [stable (j.val+1) _ (by have := j.isLt; omega) (by omega), next]
    have getLast (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
      induction l with
      | nil => rfl
      | cons h t ih => exact ih
    change ((pref j.val) ++ [_]).getD (9+j.val) false = _
    rw [← sizePref j.val (Nat.le_of_lt j.isLt), getLast]
    apply congrArg (gt j).op.eval
    apply List.map_congr_left
    intro i hi
    exact (stable j.val i (Nat.le_of_lt j.isLt) ((wiring j).1 i hi)).symm
  have out (x : Fin 9 → Bool) : V x C.output = graph x := congrFun computes x
  have validOut : 9 ≤ C.output ∧ C.output < 9+C.size := by
    constructor
    · by_contra! h
      let v : Fin 9 := ⟨C.output,h⟩
      let x : Fin 9 → Bool := fun i => decide (i = v)
      have noSingleton : ∀ (i : Fin 9), graph (fun j => decide (j = i)) = false := by decide +kernel
      have vv := inp x v
      change V x C.output = _ at vv
      rw [out, noSingleton v] at vv
      simp [x] at vv
    · by_contra! h
      let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      have sizeFold (gs : List Gate) (xs : List Bool) : (gs.foldl step xs).length = xs.length + gs.length := by
        induction gs generalizing xs with
        | nil => simp
        | cons g gs ih => rw [List.foldl_cons, ih]; simp [step]; omega
      have hx : graph (X 0) = true := by decide +kernel
      have hv := out (X 0)
      change (C.gates.foldl step (List.ofFn (X 0))).getD C.output false = _ at hv
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp only [sizeFold,List.length_ofFn]; rw [show C.gates.length = C.size from rfl]; exact h)] at hv
      rw [hx] at hv
      exact Bool.noConfusion hv
  have selmem : ∀ s, sel s ∈ ([4,6,7] : List (Fin 9)) := by decide +kernel
  choose key hkey using fun s : Fin 3 => unique (sel s) (selmem s)
  have keyIn (s : Fin 3) : (sel s).val ∈ (gt (key s)).inputs := ((hkey s).1 (key s)).mpr rfl
  have keyInj : Function.Injective key := by
    intro s t h
    have ht := keyIn t
    rw [← h] at ht
    have memNat : ∀ q, (sel q).val ∈ ([4,6,7] : List ℕ) := by decide +kernel
    have e := separated (key s) _ (keyIn s) _ ht (memNat s) (memNat t)
    have inj : ∀ a b : Fin 3, (sel a).val = (sel b).val → a = b := by decide +kernel
    exact inj _ _ e
  have agree (s : Fin 3) (x y : Fin 9 → Bool)
      (same : ∀ v, v ≠ sel s → x v = y v)
      (reader : V x (9+(key s).val) = V y (9+(key s).val)) : graph x = graph y := by
    have go (k : ℕ) (hk : k < C.size) : V x (9+k) = V y (9+k) := by
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        let j : Fin C.size := ⟨k,hk⟩
        change V x (9+j.val) = V y (9+j.val)
        by_cases e : j = key s
        · simpa [e] using reader
        rw [equation j x, equation j y]
        apply congrArg (gt j).op.eval
        apply List.map_congr_left
        intro w hw
        by_cases low : w < 9
        · let v : Fin 9 := ⟨w,low⟩
          have ne : v ≠ sel s := by
            intro eq
            apply e
            apply ((hkey s).1 j).mp
            exact (congrArg Fin.val eq) ▸ hw
          exact (inp x v).trans ((same v ne).trans (inp y v).symm)
        · have back := (wiring j).1 w hw
          change w < 9+k at back
          have eq : w = 9 + (w-9) := by omega
          rw [eq]
          exact ih (w-9) (by omega) (by omega)
    rw [← out x, ← out y]
    have outeq : C.output = 9 + (C.output-9) := by omega
    rw [outeq]
    exact go _ (by omega)
  have binary (j : Fin C.size) : ∃ a b : ℕ, (gt j).inputs = [a,b] ∧ a ≠ b ∧
      ((gt j).op = .and ∨ (gt j).op = .or) := by
    have count := ((wiring j).2.2.resolve_left fun h => noNot j h.1).2
    have nd := (wiring j).2.1
    have kind := (minimal.1 _ (List.get_mem C.gates j)).1
    change (gt j).op = .and ∨ (gt j).op = .or ∨ (gt j).op = .not at kind
    change (gt j).inputs.length = 2 at count
    change (gt j).inputs.Nodup at nd
    have arity (l : List ℕ) (h : l.length = 2) : ∃ a b, l = [a,b] := by
      cases l with
      | nil => simp at h
      | cons a t =>
        cases t with
        | nil => simp at h
        | cons b u =>
          cases u with
          | nil => exact ⟨a,b,rfl⟩
          | cons c u => simp at h
    obtain ⟨a,b,ab⟩ := arity _ count
    refine ⟨a,b,ab,by simpa [ab] using nd,?_⟩
    exact kind.elim Or.inl (fun rest => Or.inr (rest.resolve_right (noNot j)))
  have packed (s : Fin 3) : ∃ b : ℕ, b ≠ (sel s).val ∧ b < 9+(key s).val ∧
      ∀ x, V x (9+(key s).val) = (x (sel s) || V x b) := by
    obtain ⟨a,b,ab,diff,_⟩ := binary (key s)
    have reads := keyIn s
    rw [ab] at reads
    have back := (wiring (key s)).1
    change ∀ w ∈ (gt (key s)).inputs, w < 9+(key s).val at back
    rw [ab] at back
    have orPair (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by cases a <;> cases b <;> rfl
    rcases (show (sel s).val = a ∨ (sel s).val = b by simpa using reads) with ha | hb
    · subst a
      refine ⟨b,Ne.symm diff,back b (by simp),?_⟩
      intro x
      rw [equation, (show (gt (key s)).op = .or from (hkey s).2),ab]
      simp only [List.map_cons,List.map_nil,orPair,inp]
    · subst b
      refine ⟨a,diff,back a (by simp),?_⟩
      intro x
      rw [equation, (show (gt (key s)).op = .or from (hkey s).2),ab]
      simp only [List.map_cons,List.map_nil,orPair,inp,Bool.or_comm (V x a)]
  choose side sideProp using packed
  have tests : ∀ r : Fin 24, graph (X r) = (4095 : BitVec 24).getLsbD r.val := by decide +kernel
  have neg : ∀ r : Fin 24, 12 ≤ r.val → graph (X r) = false := by decide +kernel
  have up : ∀ (r : Fin 24) (s : Fin 3), 12 ≤ r.val → X r (sel s) = false →
      graph (Function.update (X r) (sel s) true) = true := by decide +kernel
  have negVal (s : Fin 3) (r : Fin 24) (hr : 12 ≤ r.val) :
      V (X r) (9+(key s).val) = X r (sel s) := by
    rcases valEq : X r (sel s) with _ | _
    · apply Bool.eq_false_iff.mpr
      intro yes
      let y := Function.update (X r) (sel s) true
      have on : V y (9+(key s).val) = true := by
        rw [(sideProp s).2.2]
        simp [y]
      have same := agree s (X r) y (fun v hv => by simp [y,Function.update_of_ne hv]) (yes.trans on.symm)
      rw [neg r hr, up r s hr valEq] at same
      exact Bool.noConfusion same
    · rw [(sideProp s).2.2,valEq]
      rfl
  let word (w : ℕ) : BitVec 24 :=
    (BitVec.ofBoolListLE (List.ofFn fun r : Fin 24 => V (X r) w)).cast (by simp)
  have bit (w : ℕ) (r : Fin 24) : (word w).getLsbD r.val = V (X r) w := by
    simp only [word,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
    rw [List.getD_eq_getElem _ _ (by simpa using r.isLt),List.getElem_ofFn]
  have raw (i : Fin 9) : word i.val = A.getD i.val 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro r hr
    rw [bit _ ⟨r,hr⟩,inp]
  have mono : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or := by
    intro g hg
    obtain ⟨j,hj⟩ := List.get_of_mem hg
    obtain ⟨_,_,_,_,h⟩ := binary j
    change (C.gates.get j).op = .and ∨ (C.gates.get j).op = .or at h
    rwa [hj] at h
  let Wins (u v : BitVec 24) := ∃ r : Fin 24,
    u.getLsbD r.val ≠ v.getLsbD r.val ∧ u.getLsbD r.val = decide (r.val < 12)
  have winsGate (k : Fin C.size) (b : ℕ) (lt : b < 9+k.val) : Wins (word (9+k.val)) (word b) := by
    obtain ⟨r,h₁,h₂⟩ := separates C minimal mono computes k b (Or.inl lt)
    exact ⟨r,by simpa only [bit] using h₁,by simpa only [bit] using h₂⟩
  have zeroWord : word (9+C.size) = 0 := by
    let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have sizeFold (gs : List Gate) (xs : List Bool) : (gs.foldl step xs).length = xs.length + gs.length := by
      induction gs generalizing xs with
      | nil => simp
      | cons g gs ih => rw [List.foldl_cons, ih]; simp [step]; omega
    apply BitVec.eq_of_getLsbD_eq
    intro r hr
    rw [bit _ ⟨r,hr⟩]
    change (C.gates.foldl step _).getD (9+C.size) false = _
    have len : C.gates.length = C.size := rfl
    rw [List.getD_eq_default _ _ (by simpa only [sizeFold,List.length_ofFn,len] using Nat.le_refl (9+C.size))]
    simp
  have winsZero (k : Fin C.size) : Wins (word (9+k.val)) 0 := by
    obtain ⟨r,h₁,h₂⟩ := separates C minimal mono computes k (9+C.size) (Or.inr rfl)
    rw [←zeroWord]
    exact ⟨r,by simpa only [bit] using h₁,by simpa only [bit] using h₂⟩
  let U (s : Fin 3) := word (9+(key s).val)
  have marked : ∀ s : Fin 3, A.getD (sel s).val 0 = M.getD s.val 0 := by decide +kernel
  have nmask (s : Fin 3) : U s &&& 16773120 = M.getD s.val 0 &&& 16773120 := by
    have off : ∀ r : Fin 24, r.val < 12 → (16773120 : BitVec 24).getLsbD r.val = false := by decide +kernel
    apply BitVec.eq_of_getLsbD_eq
    intro r hr
    rw [BitVec.getLsbD_and,BitVec.getLsbD_and]
    by_cases low : r < 12
    · have clear : (16773120 : BitVec 24).getLsbD r = false := off ⟨r,hr⟩ low
      rw [clear]
      simp
    · change ((word _).getLsbD r && _) = _
      rw [bit _ ⟨r,hr⟩,negVal s ⟨r,hr⟩ (by change 12 ≤ r; omega)]
      simp only [X,marked]
  choose a b pair different gateKind using binary
  have back (j : Fin C.size) : a j < 9+j.val ∧ b j < 9+j.val := by
    have h := (wiring j).1
    change ∀ u ∈ (gt j).inputs, u < 9+j.val at h
    rw [pair j] at h
    exact ⟨h _ (by simp),h _ (by simp)⟩
  let op (j : Fin C.size) := decide ((gt j).op = GateOp.or)
  have words (j : Fin C.size) : word (9+j.val) = if op j then word (a j) ||| word (b j) else word (a j) &&& word (b j) := by
    apply BitVec.eq_of_getLsbD_eq
    intro r hr
    rcases gateKind j with h|h
    · simp only [op,h,reduceCtorEq,decide_false,Bool.false_eq_true,↓reduceIte,BitVec.getLsbD_and]
      rw [bit _ ⟨r,hr⟩,bit _ ⟨r,hr⟩,bit _ ⟨r,hr⟩,equation,h,pair j]
      simp only [List.map_cons,List.map_nil]
      cases V (X ⟨r,hr⟩) (a j) <;> cases V (X ⟨r,hr⟩) (b j) <;> rfl
    · simp only [op,h,decide_true,↓reduceIte,BitVec.getLsbD_or]
      rw [bit _ ⟨r,hr⟩,bit _ ⟨r,hr⟩,bit _ ⟨r,hr⟩,equation,h,pair j]
      simp only [List.map_cons,List.map_nil]
      cases V (X ⟨r,hr⟩) (a j) <;> cases V (X ⟨r,hr⟩) (b j) <;> rfl
  let shifts : List (List (Fin 24)) := [
    [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23],
    [5,0,1,7,9,11,4,6,2,10,3,8,20,22,13,21,23,14,16,19,12,17,15,18],
    [11,5,0,6,10,8,9,4,1,3,7,2,12,15,22,17,18,13,23,19,20,14,21,16],
    [8,11,5,4,3,2,10,9,0,7,6,1,20,21,15,14,16,22,18,19,12,13,17,23],
    [2,8,11,9,7,1,3,10,5,6,4,0,12,17,21,13,23,15,16,19,20,22,14,18],
    [1,2,8,10,6,0,7,3,11,4,9,5,20,14,17,22,18,21,23,19,12,15,13,16]]
  let perm (t : Fin 6) (r : Fin 24) := ((shifts.getD t.val []).getD r.val 0)
  let T (t : Fin 6) (w : BitVec 24) : BitVec 24 :=
    (BitVec.ofBoolListLE (List.ofFn fun r : Fin 24 => w.getLsbD (perm t r).val)).cast (by simp)
  have tbit (t : Fin 6) (w : BitVec 24) (r : Fin 24) :
      (T t w).getLsbD r.val = w.getLsbD (perm t r).val := by
    simp only [T,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
    rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
  have rotatesWins (t : Fin 6) (u v : BitVec 24) (h : Wins u v) : Wins (T t u) (T t v) := by
    have inv : ∀ (k : Fin 6) (r : Fin 24),
        perm k (perm (-k) r) = r ∧ decide ((perm (-k) r).val < 12) = decide (r.val < 12) := by decide +kernel
    obtain ⟨r,hd,hs⟩ := h
    obtain ⟨hq,sg⟩ := inv t r
    refine ⟨perm (-t) r,?_,?_⟩
    · rwa [tbit,tbit,hq]
    · rwa [tbit,hq,sg]
  have rotZero (t : Fin 6) : T t 0 = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro r hr
    rw [tbit _ _ ⟨r,hr⟩]
    simp
  have tAnd (t : Fin 6) (a b : BitVec 24) : T t (a &&& b) = T t a &&& T t b := by
    apply BitVec.eq_of_getLsbD_eq
    intro r hr
    rw [tbit _ _ ⟨r,hr⟩,BitVec.getLsbD_and,BitVec.getLsbD_and,tbit _ _ ⟨r,hr⟩,tbit _ _ ⟨r,hr⟩]
  have tOr (t : Fin 6) (a b : BitVec 24) : T t (a ||| b) = T t a ||| T t b := by
    apply BitVec.eq_of_getLsbD_eq
    intro r hr
    rw [tbit _ _ ⟨r,hr⟩,BitVec.getLsbD_or,BitVec.getLsbD_or,tbit _ _ ⟨r,hr⟩,tbit _ _ ⟨r,hr⟩]
  have constants : ∀ t : Fin 6, T t 4095 = 4095 ∧ T t 16773120 = 16773120 := by decide +kernel
  let rawPerms : List (List (Fin 9)) := [[0, 1, 2, 3, 4, 5, 6, 7, 8], [1, 2, 3, 8, 6, 0, 7, 4, 5], [2, 3, 8, 5, 7, 1, 4, 6, 0], [3, 8, 5, 0, 4, 2, 6, 7, 1], [8, 5, 0, 1, 6, 3, 7, 4, 2], [5, 0, 1, 2, 7, 8, 4, 6, 3]]
  let rawPerm (t : Fin 6) (i : Fin 9) := (rawPerms.getD t.val []).getD i.val 0
  have rawRot : ∀ (t : Fin 6) (i : Fin 9), T t (A.getD i.val 0) = A.getD (rawPerm t i).val 0 := by decide +kernel
  have backRaw : ∀ (t : Fin 6) (i : Fin 9), rawPerm (-t) (rawPerm t i) = i := by decide +kernel
  let tags : List ℕ := [4,6,7]
  have tagRaw : ∀ (t : Fin 6) (i : Fin 9), (rawPerm t i).val ∈ tags ↔ i.val ∈ tags := by decide +kernel
  let rename (t : Fin 6) (u : ℕ) := if h : u<9 then (rawPerm t ⟨u,h⟩).val else u
  have renRaw (t : Fin 6) (i : Fin 9) : rename t i.val = (rawPerm t i).val := by simp only [rename,i.isLt,↓reduceDIte]
  have unrename (t : Fin 6) (u : ℕ) : rename (-t) (rename t u) = u := by
    by_cases hu : u<9
    · let i : Fin 9 := ⟨u,hu⟩
      change rename (-t) (rename t i.val) = i.val
      rw [renRaw,renRaw,backRaw]
    · simp [rename,hu]
  have renInj (t : Fin 6) : Function.Injective (rename t) := fun u v h => by
    simpa only [unrename] using congrArg (rename (-t)) h
  have stable (t : Fin 6) (i : ℕ) : rename t (9+i) = 9+i := by simp [rename]
  have renLt (t : Fin 6) (u k : ℕ) (h : u<9+k) : rename t u<9+k := by
    by_cases low : u<9
    · have q := (rawPerm t ⟨u,low⟩).isLt
      simp only [rename,low,↓reduceDIte]; omega
    · simpa [rename,low] using h
  have renTag (t : Fin 6) (u : ℕ) : rename t u ∈ tags ↔ u ∈ tags := by
    by_cases h : u<9
    · simpa only [rename,h,↓reduceDIte] using tagRaw t ⟨u,h⟩
    · simp [rename,h]
  let j0 : Fin C.size := ⟨0,by have := (key 0).isLt;omega⟩
  have firstFree (t : Fin 3) : j0 ≠ key t := by
    intro eq
    have bounds := (sideProp t).2.1
    rw [←eq] at bounds
    change side t < 9+0 at bounds
    let i : Fin 9 := ⟨side t,by omega⟩
    have sep : ∀ (s : Fin 3) (v : Fin 9), v ≠ sel s →
        ∃ r : Fin 24, 12 ≤ r.val ∧ X r v = true ∧ X r (sel s) = false := by decide +kernel
    obtain ⟨r,hr,on,off⟩ := sep t i (fun h => (sideProp t).1 (congrArg Fin.val h))
    have bad := negVal t r hr
    rw [(sideProp t).2.2,show V (X r) (side t)=X r i from inp _ i,on,off] at bad
    contradiction
  have noTag (w : ℕ) (hw : w ∈ (gt j0).inputs) : w ∉ tags := by
    intro h
    have cover : ∀ s ∈ tags, ∃ t : Fin 3, (sel t).val=s := by decide +kernel
    obtain ⟨t,rfl⟩ := cover w h
    exact firstFree t (((hkey t).1 j0).mp hw)
  have firstOrbit : ∃ t : Fin 6, T t (word 9) ∈ ([1,14053491,7684279,5689661] : List (BitVec 24)) := by
    let i : Fin 9 := ⟨a j0,(back j0).1⟩
    let j : Fin 9 := ⟨b j0,(back j0).2⟩
    have ip : i.val ∉ tags := noTag _ (by rw [pair]; simp [i])
    have jp : j.val ∉ tags := noTag _ (by rw [pair]; simp [j])
    have ij : i ≠ j := fun h => different j0 (congrArg Fin.val h)
    have first := words j0
    change word 9 = if op j0 then word i.val ||| word j.val else word i.val &&& word j.val at first
    rw [raw,raw] at first
    let orbitTable : List (List (Fin 6)) := [[0, 0, 0, 0, 0, 1, 0, 0, 2], [0, 0, 5, 5, 0, 1, 0, 0, 2], [0, 5, 0, 4, 0, 1, 0, 0, 4], [0, 5, 4, 0, 0, 3, 0, 0, 3], [0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 3, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [2, 2, 4, 3, 0, 2, 0, 0, 0]]
    let pick (i j : Fin 9) := (orbitTable.getD i.val []).getD j.val 0
    let seeds : List (BitVec 24) := [1,14053491,7684279,5689661]
    let allowed (i j : Fin 9) := (!tags.contains i.val && !tags.contains j.val && (i != j))
    have orbit : ∀ (i j : Fin 9),
        (!allowed i j || (seeds.contains (T (pick i j) (A.getD i.val 0 ||| A.getD j.val 0)) &&
        ((A.getD i.val 0 &&& A.getD j.val 0 &&& 4095 == 0) ||
        seeds.contains (T (pick i j) (A.getD i.val 0 &&& A.getD j.val 0))))) = true := by decide +kernel
    have allow : allowed i j = true := by simp [allowed,ip,jp,ij]
    have tests := orbit i j
    simp only [allow,Bool.not_true,Bool.false_or,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,List.contains_iff_mem] at tests
    have lit : word 9 &&& 4095 ≠ 0 := by
      obtain ⟨r,hd,hp⟩ := winsZero j0
      change (word 9).getLsbD r.val ≠ (0 : BitVec 24).getLsbD r.val at hd
      change (word 9).getLsbD r.val = decide (r.val<12) at hp
      have zb : ∀ r : Fin 24, (0 : BitVec 24).getLsbD r.val = false := by decide +kernel
      have on : (word 9).getLsbD r.val = true := by
        cases e : (word 9).getLsbD r.val
        · exact (hd (by rw [e,zb r])).elim
        · rfl
      have hl : r.val<12 := of_decide_eq_true (hp.symm.trans on)
      have low : ∀ r : Fin 24, r.val < 12 → (4095 : BitVec 24).getLsbD r.val = true := by decide +kernel
      intro h
      have bad := congrArg (fun w : BitVec 24 => w.getLsbD r.val) h
      change (word 9 &&& 4095).getLsbD r.val = (0 : BitVec 24).getLsbD r.val at bad
      rw [BitVec.getLsbD_and,on,low r hl,zb r] at bad
      contradiction
    rw [first] at lit ⊢
    cases h : op j0
    · refine ⟨pick i j,tests.2.resolve_left ?_⟩
      simpa only [h,Bool.false_eq_true,↓reduceIte] using lit
    · exact ⟨pick i j,tests.1⟩
  obtain ⟨t,seed⟩ := firstOrbit
  let inputs (i : Fin (9+C.size)) := T t (word (rename (-t) i.val))
  let v (i : ℕ) := (List.ofFn inputs).getD i 0
  have value (i : ℕ) (hi : i < 9+C.size) : v i = T t (word (rename (-t) i)) := by
    unfold v
    rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_ofFn]
  have atRen (i : ℕ) (hi : i < 9+C.size) : v (rename t i) = T t (word i) := by rw [value _ (renLt t _ _ hi),unrename]
  have atGate (j : Fin C.size) : v (9+j.val) = T t (word (9+j.val)) := by rw [value _ (by have := j.isLt;omega),stable]
  have past : v (9+C.size) = 0 := by
    apply List.getD_eq_default
    simp
  have outputWord : word C.output = 4095 := by
    apply BitVec.eq_of_getLsbD_eq
    intro r hr
    rw [bit _ ⟨r,hr⟩,out,tests ⟨r,hr⟩]
  let last : Fin C.size := ⟨C.output-9,by have h := validOut; omega⟩
  have endAt : 9+last.val = C.output := by dsimp [last]; have h := validOut; omega
  refine exclude C.size small inputs (fun j => rename t (a j)) (fun j => rename t (b j)) op ?_ ?_ ?_ ?_ ?_ ?_ last ?_
  · intro i
    change v i.val = _
    rw [value _ (by have := i.isLt;omega)]
    rw [renRaw,raw,rawRot,show rawPerm t (rawPerm (-t) i) = i by simpa using backRaw (-t) i]
  · have h : v 9 = T t (word 9) := atGate j0
    change v 9 ∈ _
    rwa [h]
  · intro j
    obtain ⟨ha,hb⟩ := back j
    refine ⟨renLt _ _ _ ha,renLt _ _ _ hb,fun h => different j ((renInj t) h),?_⟩
    change v (9+j.val) = if op j then v (rename t (a j)) ||| v (rename t (b j)) else v (rename t (a j)) &&& v (rename t (b j))
    rw [atGate,atRen _ (by have := j.isLt;omega),atRen _ (by have := j.isLt;omega),words]
    cases op j <;> simp only [Bool.false_eq_true,↓reduceIte,tAnd,tOr]
  · intro s hs
    have old : rename (-t) s ∈ tags := (renTag _ _).mpr hs
    have cover : ∀ s ∈ tags, ∃ t : Fin 3, (sel t).val=s := by decide +kernel
    obtain ⟨k,eq⟩ := cover _ old
    have sEq : rename t (sel k).val = s := by rw [eq]; simpa using unrename (-t) s
    rw [←sEq]
    refine ⟨key k,?_,show op (key k) = true from decide_eq_true (show (gt (key k)).op = .or from (hkey k).2),?_⟩
    · intro j
      have h := (hkey k).1 j
      change (sel k).val ∈ (gt j).inputs ↔ j=key k at h
      rw [pair j] at h
      change (rename t (a j)=rename t (sel k).val ∨ rename t (b j)=rename t (sel k).val) ↔ j=key k
      simpa only [(renInj t).eq_iff,List.mem_cons,List.not_mem_nil,or_false,eq_comm (a := (sel k).val)] using h
    · change v (9+(key k).val) &&& _ = v (rename t (sel k).val) &&& _
      rw [atGate,atRen _ (by have := (sel k).isLt;omega)]
      have mask := congrArg (T t) (nmask k)
      rw [raw,marked]
      simpa only [tAnd,(constants t).2,U] using mask
  · intro j ha hb
    apply congrArg (rename t)
    apply separated j (a j) _ (b j) _ ((renTag _ _).mp ha) ((renTag _ _).mp hb) <;> change _ ∈ (gt j).inputs <;> rw [pair j] <;> simp
  · intro j i bound
    change Wins (v (9+j.val)) (v i)
    rw [atGate]
    rcases bound with h|rfl
    · rw [value _ (by have := j.isLt;omega)]
      exact rotatesWins t _ _ (winsGate j _ (renLt _ _ _ h))
    · rw [past]
      simpa only [rotZero] using rotatesWins t _ _ (winsZero j)
  · change v (9+last.val) = 4095
    rw [atGate,endAt,outputWord,(constants t).1]
