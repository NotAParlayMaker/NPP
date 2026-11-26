import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18265_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

abbrev Ref := Sum Bool ℕ
def zero : Ref := .inl false

def val (w : List Bool) : Ref → Bool
  | .inl b => b
  | .inr j => w.getD j false

def valid (k : ℕ) : Ref → Prop
  | .inl _ => True
  | .inr j => j < k

def idxs (ls : List Ref) : List ℕ := ls.filterMap (fun s => s.elim (fun _ => none) some)

def compile : GateOp → List Ref → Gate
  | .and, ls =>
    if .inl false ∈ ls then ⟨.or,[]⟩ else ⟨.and,idxs ls⟩
  | _, ls =>
    if .inl true ∈ ls then ⟨.and,[]⟩ else ⟨.or,idxs ls⟩

theorem idxsLength (ls : List Ref) : (idxs ls).length ≤ ls.length := List.length_filterMap_le _ _

theorem idxsAll (w : List Bool) (ls : List Ref) :
    (ls.map (val w)).all id =
      (if .inl false ∈ ls then false else ((idxs ls).map (fun i => w.getD i false)).all id) := by
  induction ls with
  | nil => rfl
  | cons a ls ih =>
    cases a with
    | inl b => cases b <;> simp [val,idxs,ih]
    | inr j => by_cases hz : Sum.inl false ∈ ls <;> simp [val,idxs,ih,hz]

theorem idxsAny (w : List Bool) (ls : List Ref) :
    (ls.map (val w)).any id =
      (if .inl true ∈ ls then true else ((idxs ls).map (fun i => w.getD i false)).any id) := by
  induction ls with
  | nil => rfl
  | cons a ls ih =>
    cases a with
    | inl b => cases b <;> simp [val,idxs,ih]
    | inr j => by_cases hz : Sum.inl true ∈ ls <;> simp [val,idxs,ih,hz]

theorem compileLaw (w : List Bool) (op : GateOp) (h : op = .and ∨ op = .or) (ls : List Ref) :
    (compile op ls).op.eval ((compile op ls).inputs.map (fun i => w.getD i false)) =
      op.eval (ls.map (val w)) := by
  rcases h with rfl | rfl
  · rw [GateOp.eval,idxsAll]; by_cases hz : Sum.inl false ∈ ls <;> simp [compile,hz,GateOp.eval]
  · rw [GateOp.eval,idxsAny]; by_cases hz : Sum.inl true ∈ ls <;> simp [compile,hz,GateOp.eval]

theorem compileOK (op : GateOp) (ls : List Ref) (hs : ls.length ≤ 2) :
    (compile op ls).op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ (compile op ls).inputs.length ≤ 2 := by
  have le := (idxsLength ls).trans hs
  cases op <;> simp only [compile] <;> split <;> simp [le]

def run (g : List Gate) (x : List Bool) := (Circuit.mk g 0).wires x

theorem runLength (g : List Gate) (x : List Bool) : (run g x).length = x.length+g.length := by
  change (g.foldl _ x).length = x.length+g.length
  induction g generalizing x with
  | nil => simp
  | cons gate g ih => rw [List.foldl_cons,ih]; simp; omega

theorem runApp (g h : List Gate) (x : List Bool) : run (g++h) x = run h (run g x) := by
  simp [run,Circuit.wires,List.foldl_append]

theorem runSingle (g : List Gate) (a : Gate) (x : List Bool) :
    run (g++[a]) x = run g x ++ [a.op.eval (a.inputs.map (fun i => (run g x).getD i false))] := by rw [runApp]; rfl

theorem runPrefix (g : List Gate) (x : List Bool) : ∃ t, run g x = x++t := by
  induction g generalizing x with
  | nil => exact ⟨[],by simp [run,Circuit.wires]⟩
  | cons a gs ih =>
    obtain ⟨t,ht⟩ := ih (x++[a.op.eval (a.inputs.map (fun j => x.getD j false))])
    refine ⟨a.op.eval (a.inputs.map (fun j => x.getD j false))::t,?_⟩
    change run gs (x++[_]) = _
    rw [ht,List.append_assoc,List.singleton_append]

theorem runBefore (g h : List Gate) (x : List Bool) (i : ℕ) (hi : i < (run g x).length) :
    (run (g++h) x).getD i false = (run g x).getD i false := by
  obtain ⟨t,ht⟩ := runPrefix h (run g x)
  rw [runApp,ht]
  exact List.getD_append _ _ _ _ hi

theorem getDOut {α : Type} (xs : List α) (i : ℕ) (d : α) (h : xs.length ≤ i) : xs.getD i d = d := by
  simp [List.getD,List.getElem?_eq_none h]

theorem valCong {w : List Bool} (t : List Bool) (s : Ref) (h : valid w.length s) :
    val (w++t) s = val w s := by
  cases s with
  | inl b => rfl
  | inr i => exact List.getD_append _ _ _ _ h

theorem validMono {a b : ℕ} (h : a ≤ b) (s : Ref) (hs : valid a s) : valid b s := by
  cases s with
  | inl q => trivial
  | inr i => exact lt_of_lt_of_le hs h

theorem getDLast {α : Type} (l : List α) (a d : α) (i : ℕ) (h : i=l.length) :
    (l++[a]).getD i d = a := by subst i; simp

theorem getDOther {α : Type} (l : List α) (a d : α) (i : ℕ) (h : i≠l.length) :
    (l++[a]).getD i d = l.getD i d := by
  by_cases hi : i < l.length
  · exact List.getD_append _ _ _ _ hi
  · rw [getDOut _ _ _ (by simp; omega),getDOut _ _ _ (by omega)]

theorem addRef (k : ℕ) (g : List Gate) (refs : List Ref) (h : ∀ i, valid (k+g.length) (refs.getD i zero))
    (s : Ref) (t : List Gate) (hs : valid (k+(g++t).length) s) :
    ∀ i, valid (k+(g++t).length) ((refs++[s]).getD i zero) := by
  intro i
  by_cases he : i = refs.length
  · rw [getDLast _ _ _ _ he]; exact hs
  · rw [getDOther _ _ _ _ he]
    apply validMono _ _ (h i)
    simp

theorem addEval (x old : List Bool) (g t : List Gate) (refs : List Ref)
    (len : refs.length = old.length) (hd : ∀ i, valid (run g x).length (refs.getD i zero))
    (ev : ∀ i, val (run g x) (refs.getD i zero) = old.getD i false)
    (s : Ref) (b : Bool) (eb : val (run (g++t) x) s = b) :
    ∀ i, val (run (g++t) x) ((refs++[s]).getD i zero) = (old++[b]).getD i false := by
  intro i
  by_cases eq : i = refs.length
  · rw [getDLast _ _ _ _ eq,getDLast _ _ _ _ (eq.trans len)]
    exact eb
  · rw [getDOther _ _ _ _ eq,getDOther _ _ _ _ (by rwa [← len])]
    obtain ⟨v,hv⟩ := runPrefix t (run g x)
    rw [runApp,hv,valCong _ _ (hd i),ev i]

theorem takenCount (K : Finset ℕ) (j : ℕ) :
    (K.filter (fun i => i < j+1)).card = (K.filter (fun i => i < j)).card + if j ∈ K then 1 else 0 := by
  by_cases hj : j ∈ K
  · have eq : K.filter (fun i => i < j+1) = insert j (K.filter (fun i => i < j)) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨hi,hp⟩
        by_cases e : i=j
        · exact Or.inl e
        · exact Or.inr ⟨hi,by omega⟩
      · rintro (rfl | ⟨hi,hp⟩)
        · exact ⟨hj,by omega⟩
        · exact ⟨hi,by omega⟩
    rw [eq,Finset.card_insert_of_notMem (by simp)]
    simp [hj]
  · have eq : K.filter (fun i => i < j+1) = K.filter (fun i => i < j) := by
      ext i
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hi,hp⟩
        have ne : i ≠ j := fun h => hj (h ▸ hi)
        exact ⟨hi,by omega⟩
      · rintro ⟨hi,hp⟩
        exact ⟨hi,by omega⟩
    rw [eq]
    simp [hj]

def removable {n m : ℕ} (C : Circuit) (ZL : Finset (Fin n)) (ZR : Finset (Fin m)) (j : ℕ) (s : Ref) : Prop :=
  ∀ (u : Fin n) (v : Fin m), u ∉ ZL → v ∉ ZR →
    val (C.wires (oneEach u v)) s = (C.wires (oneEach u v)).getD (n+m+j) false

theorem removeAll {n m : ℕ} (A : Fin n → Fin m → Bool) (C : Circuit)
    (ZL : Finset (Fin n)) (ZR : Finset (Fin m)) (K : Finset ℕ)
    (hc : Monotone2 C) (he : Represents A C)
    (hK : ∀ j ∈ K, j < C.gates.length ∧ n+m+j ≠ C.output ∧
      ∃ s : Ref, valid (n+m+j) s ∧ removable C ZL ZR j s) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + K.card ≤ C.size ∧
      ∀ (u : Fin n) (v : Fin m), u ∉ ZL → v ∉ ZR → D.eval (oneEach u v) = A u v := by
  let N := n+m
  have inputLength (u : Fin n) (v : Fin m) : (oneEach u v).length = N := by simp [oneEach,N]
  have construct (j : ℕ) (hj : j ≤ C.gates.length) :
      ∃ g : List Gate, ∃ refs : List Ref,
        Monotone2 (⟨g,0⟩ : Circuit) ∧ refs.length = N+j ∧
        g.length + (K.filter (fun i => i < j)).card = j ∧
        (∀ i, valid (N+g.length) (refs.getD i zero)) ∧
        (∀ i < N+j, (i < N ∨ i-N ∉ K) → ∃ k, refs.getD i zero = Sum.inr k) ∧
        ∀ (u : Fin n) (v : Fin m), u ∉ ZL → v ∉ ZR → ∀ i,
          val (run g (oneEach u v)) (refs.getD i zero) =
            (run (C.gates.take j) (oneEach u v)).getD i false := by
    induction j with
    | zero =>
      let refs : List Ref := (List.range N).map Sum.inr
      have rl : refs.length = N := by simp [refs]
      have get (i : ℕ) (h : i<N) : refs.getD i zero = Sum.inr i := by
        simp [refs,List.getD,List.getElem?_range h]
      refine ⟨[],refs,by intro g h; simp at h,by simpa using rl,by simp,?_,?_,?_⟩
      · intro i
        by_cases hi : i<N
        · rw [get i hi]; simpa [valid] using hi
        · rw [getDOut _ _ _ (by omega)]; trivial
      · intro i hi _
        exact ⟨i,get i (by omega)⟩
      · intro u v _ _ i
        by_cases hi : i<N
        · rw [get i hi]; rfl
        · rw [getDOut _ _ _ (by omega)]
          change false = (oneEach u v).getD i false
          rw [getDOut _ _ _ (by rw [inputLength]; omega)]
    | succ j ih =>
      have lt : j<C.gates.length := by omega
      obtain ⟨g,refs,mg,len,cnt,vd,kept,ev⟩ := ih (by omega)
      let a := C.gates[j]
      let P := C.gates.take j
      have snoc : C.gates.take (j+1) = P++[a] := List.take_succ_eq_append_getElem lt
      have plen : P.length = j := by simp [P,Nat.min_eq_left lt.le]
      have count := takenCount K j
      have finish (t : List Gate) (s : Ref) (hg : Monotone2 (⟨g++t,0⟩ : Circuit))
          (hs : valid (N+(g++t).length) s)
          (cl : (g++t).length+(K.filter (fun i => i < j+1)).card=j+1)
          (sk : j ∉ K → ∃ k, s = Sum.inr k)
          (evaluate : ∀ u v, u ∉ ZL → v ∉ ZR →
            let x := oneEach u v
            val (run (g++t) x) s = a.op.eval (a.inputs.map (fun i => (run P x).getD i false))) :
          ∃ g' : List Gate, ∃ refs' : List Ref,
            Monotone2 (⟨g',0⟩ : Circuit) ∧ refs'.length = N+(j+1) ∧
            g'.length+(K.filter (fun i => i<j+1)).card=j+1 ∧
            (∀ i, valid (N+g'.length) (refs'.getD i zero)) ∧
            (∀ i<N+(j+1), (i<N ∨ i-N∉K) → ∃ k, refs'.getD i zero=Sum.inr k) ∧
            ∀ (u : Fin n) (v : Fin m), u∉ZL → v∉ZR → ∀ i,
              val (run g' (oneEach u v)) (refs'.getD i zero) =
                (run (C.gates.take (j+1)) (oneEach u v)).getD i false := by
        refine ⟨g++t,refs++[s],hg,by simp [len];omega,cl,addRef N g refs vd s t hs,?_,?_⟩
        · intro i bi ri
          by_cases eq : i=refs.length
          · rw [getDLast _ _ _ _ eq]
            have dif : i-N=j := by omega
            exact sk (dif ▸ ri.resolve_left (by omega))
          · rw [getDOther _ _ _ _ eq]
            exact kept i (by omega) ri
        · intro u v hu hv i
          rw [snoc,runSingle]
          exact addEval (oneEach u v) _ g t refs (by rw [runLength,inputLength,plen,len])
            (by rw [runLength,inputLength]; exact vd) (ev u v hu hv) _ _ (evaluate u v hu hv) i
      by_cases pj : j∈K
      · obtain ⟨_,_,s,sv,sm⟩ := hK j pj
        let sr := s.elim Sum.inl (fun i => refs.getD i zero)
        apply finish [] sr (by simpa using mg)
        · simp only [List.append_nil]
          cases s with
          | inl b => trivial
          | inr i => exact vd i
        · simp only [List.append_nil,count,ite_eq_left pj]; omega
        · exact fun h => False.elim (h pj)
        · intro u v hu hv
          let x := oneEach u v
          have hx : x.length=N := inputLength u v
          have xlen : (run P x).length=N+j := by rw [runLength,hx,plen]
          have whole : ∀ i<(run (P++[a]) x).length,
              (C.wires x).getD i false = (run (P++[a]) x).getD i false := by
            intro i hi
            have eq : (P++[a])++C.gates.drop (j+1) = C.gates := by rw [←snoc,List.take_append_drop]
            rw [← show run C.gates x = C.wires x from rfl,← eq]
            exact runBefore _ _ _ _ hi
          have oldv := whole (N+j) (by rw [runLength,hx,List.length_append,plen];simp)
          rw [runSingle,getDLast _ _ _ _ xlen.symm] at oldv
          have hvv : val (run g x) sr = val (C.wires x) s := by
            cases s with
            | inl b => rfl
            | inr i =>
              have si : i<N+j := sv
              change val (run g x) (refs.getD i zero) = _
              rw [ev u v hu hv i]
              change (run P x).getD i false = (C.wires x).getD i false
              rw [whole i (by rw [runLength,hx,List.length_append,plen]; simp; omega),
                runBefore _ _ _ _ (by omega)]
          simpa only [List.append_nil] using hvv.trans ((sm u v hu hv).trans oldv)
      · let a' := compile a.op (a.inputs.map fun i => refs.getD i zero)
        have ok := hc a (List.getElem_mem lt)
        have hok : a.op = .and ∨ a.op = .or := by simpa using ok.1
        have da := compileOK a.op (a.inputs.map fun i => refs.getD i zero) (by simpa using ok.2)
        apply finish [a'] (Sum.inr (N+g.length))
        · intro q mq
          rcases List.mem_append.mp mq with h | h
          · exact mg _ h
          · obtain rfl := List.mem_singleton.mp h
            exact da
        · simp [valid]
        · simp only [List.length_append,List.length_singleton,count,ite_eq_right pj]
          omega
        · exact fun _ => ⟨_,rfl⟩
        · intro u v hu hv
          let x := oneEach u v
          change (run (g++[a']) x).getD (N+g.length) false = _
          rw [runSingle,getDLast _ _ _ _ (by rw [runLength,inputLength])]
          unfold a'
          rw [compileLaw _ _ hok,List.map_map]
          congr 1
          apply List.map_congr_left
          intro i _
          exact ev u v hu hv i
  obtain ⟨g,refs,mg,len,cnt,vd,kept,ev⟩ := construct C.gates.length le_rfl
  have allK : K.filter (fun i => i<C.gates.length) = K := Finset.filter_eq_self.mpr
    (fun j hj => (hK j hj).1)
  rw [allK] at cnt
  have evalOut (u : Fin n) (v : Fin m) (hu : u∉ZL) (hv : v∉ZR) :
      val (run g (oneEach u v)) (refs.getD C.output zero) = A u v := by
    rw [ev u v hu hv,List.take_length]
    exact he u v
  by_cases inside : C.output<N+C.gates.length
  · have keeps : C.output<N ∨ C.output-N∉K := by
      by_cases hi : C.output<N
      · exact Or.inl hi
      · right
        intro mem
        exact (hK (C.output-N) mem).2.1 (by omega)
    obtain ⟨k,hk⟩ := kept C.output inside keeps
    refine ⟨⟨g,k⟩,mg,by exact cnt.le,?_⟩
    intro u v hu hv
    have e := evalOut u v hu hv
    rw [hk] at e
    exact e
  · refine ⟨⟨g,N+g.length⟩,mg,by exact cnt.le,?_⟩
    intro u v hu hv
    have e := evalOut u v hu hv
    rw [getDOut _ _ _ (by omega)] at e
    change (run g (oneEach u v)).getD (N+g.length) false = _
    rw [getDOut _ _ _ (by rw [runLength,inputLength])]
    exact e

end PEqualNP.Outside.L_meta_18265_aux


theorem PEqualNP.Outside.L_meta_18265 :
∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (ZL : Finset (Fin n)) (ZR : Finset (Fin m))
  (K : Finset ℕ), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.Represents.Represents A C →
  (∀ j ∈ K, j < C.gates.length ∧ n + m + j ≠ C.output ∧
    ((∃ b : Bool, ∀ (u : Fin n) (v : Fin m), u ∉ ZL → v ∉ ZR →
        (C.wires (PEqualNP.Represents.oneEach u v)).getD (n + m + j) false = b) ∨
     (∃ w < n + m + j, ∀ (u : Fin n) (v : Fin m), u ∉ ZL → v ∉ ZR →
        (C.wires (PEqualNP.Represents.oneEach u v)).getD (n + m + j) false =
          (C.wires (PEqualNP.Represents.oneEach u v)).getD w false))) →
  ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧ C'.size + K.card ≤ C.size ∧
    ∀ (u : Fin n) (v : Fin m), u ∉ ZL → v ∉ ZR → C'.eval (PEqualNP.Represents.oneEach u v) = A u v := by
  intro n m A C ZL ZR K mono repr h
  apply PEqualNP.Outside.L_meta_18265_aux.removeAll A C ZL ZR K mono repr
  intro j hj
  obtain ⟨len,output,choice⟩ := h j hj
  refine ⟨len,output,?_⟩
  rcases choice with ⟨b,hb⟩ | ⟨i,hi,hh⟩
  · exact ⟨Sum.inl b, trivial,fun u v hu hv => (hb u v hu hv).symm⟩
  · exact ⟨Sum.inr i, hi,fun u v hu hv => (hh u v hu hv).symm⟩
