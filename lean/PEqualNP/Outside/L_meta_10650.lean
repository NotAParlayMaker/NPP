import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_10650_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev BFn (n:ℕ):=(Fin n -> Bool) -> Bool
def wiresFrom (gs:List Gate) (w:List Bool):List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
theorem wiresFrom_append (gs gs':List Gate) (w:List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w):=by
  simp [wiresFrom,List.foldl_append]
theorem wiresFrom_prefix (gs:List Gate):∀ w:List Bool,
    ∃ t:List Bool,wiresFrom gs w = w ++ t /\ t.length = gs.length:=by
  induction gs with
  | nil => intro w; exact ⟨[],by simp [wiresFrom],rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t,ht,hl⟩:=ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t,?_,by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp
theorem length_wiresFrom (gs:List Gate) (w:List Bool) :
    (wiresFrom gs w).length = w.length + gs.length:=by
  obtain ⟨t,ht,hl⟩:=wiresFrom_prefix gs w
  rw [ht]; simp [hl]
theorem getD_wiresFrom (gs:List Gate) (w:List Bool) (i:ℕ) (h:i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false:=by
  obtain ⟨t,ht,_⟩:=wiresFrom_prefix gs w
  rw [ht,List.getD_append _ _ _ _ h]
theorem getD_snoc_ne {α:Type} (L:List α) (S d:α) (j:ℕ) (h:j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d:=by
  by_cases hj:j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]
theorem getD_snoc_eq {α:Type} (L:List α) (S d:α):(L ++ [S]).getD L.length d = S:=by
  simp
theorem getD_snoc_len {α:Type} (L:List α) (S d:α) (k:ℕ) (h:L.length = k) :
    (L ++ [S]).getD k d = S:=by
  subst h; simp
def Ok (g:Gate):Prop :=
  (g.op = GateOp.and \/ g.op = GateOp.or \/ g.op = GateOp.not) /\ g.inputs.length ≤ 2
abbrev Stat:=Sum Bool ℕ
def statVal (w:List Bool):Stat -> Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false
def statValid (m:ℕ):Stat -> Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m
theorem statValid_mono {m m':ℕ} (h:m ≤ m'):∀ s,statValid m s -> statValid m' s
  | Sum.inl _,_ => trivial
  | Sum.inr _,hj => Nat.lt_of_lt_of_le hj h
def simpNot (m:ℕ):List Stat -> Option Gate × Stat
  | [] => (none,Sum.inl true)
  | Sum.inl c :: _ => (none,Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not,[j]⟩,Sum.inr m)
def simpAnd (m:ℕ):List Stat -> Option Gate × Stat
  | [] => (none,Sum.inl true)
  | [Sum.inl c] => (none,Sum.inl c)
  | [Sum.inr j] => (none,Sum.inr j)
  | [Sum.inl c,Sum.inl d] => (none,Sum.inl (c && d))
  | [Sum.inl c,Sum.inr j] => (none,bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j,Sum.inl c] => (none,bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j,Sum.inr k] => (some ⟨GateOp.and,[j,k]⟩,Sum.inr m)
  | _ => (none,Sum.inl false)
def simpOr (m:ℕ):List Stat -> Option Gate × Stat
  | [] => (none,Sum.inl false)
  | [Sum.inl c] => (none,Sum.inl c)
  | [Sum.inr j] => (none,Sum.inr j)
  | [Sum.inl c,Sum.inl d] => (none,Sum.inl (c || d))
  | [Sum.inl c,Sum.inr j] => (none,bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j,Sum.inl c] => (none,bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j,Sum.inr k] => (some ⟨GateOp.or,[j,k]⟩,Sum.inr m)
  | _ => (none,Sum.inl false)
def simplify (op:GateOp) (m:ℕ) (ins:List Stat):Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none,Sum.inl false)
def CleanG (m:ℕ) (g:Gate):Prop :=
  (g.op = GateOp.not /\ ∃ j,j < m /\ g.inputs = [j]) \/
  ((g.op = GateOp.and \/ g.op = GateOp.or) /\ ∃ j k,j < m /\ k < m /\ g.inputs = [j,k])
theorem cleanG_lt {m:ℕ} {g:Gate} (h:CleanG m g):∀ a ∈ g.inputs,a < m:=by
  rcases h with ⟨_,j,hj,hin⟩ | ⟨_,j,k,hj,hk,hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega
def CleanL (n:ℕ) (gs:List Gate):Prop :=
  ∀ p g,gs[p]? = some g -> CleanG (n + p) g
theorem simplify_clean (op:GateOp) (m:ℕ) (ins:List Stat)
    (hv:∀ s ∈ ins,statValid m s) :
    ∀ g ∈ (simplify op m ins).1,CleanG m g:=by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact Or.inr ⟨Or.inl rfl,_,_,hv (Sum.inr _) (by simp),hv (Sum.inr _) (by simp),rfl⟩
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact Or.inr ⟨Or.inr rfl,_,_,hv (Sum.inr _) (by simp),hv (Sum.inr _) (by simp),rfl⟩
  · rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl,_,hv (Sum.inr _) (by simp),rfl⟩
  · simp at hg
  · simp at hg
theorem simplify_op (op:GateOp) (m:ℕ) (ins:List Stat) :
    ∀ g ∈ (simplify op m ins).1,g.op = op:=by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg; subst hg; rfl
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg; subst hg; rfl
  · rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;> simp [simpNot] at hg; subst hg; rfl
  · simp at hg
  · simp at hg
theorem simplify_none_of_inl_clean (op:GateOp) (m:ℕ) (ins:List Stat)
    (hok:(op = GateOp.not /\ ∃ a,ins = [a]) \/ ((op = GateOp.and \/ op = GateOp.or) /\ ∃ a b,ins = [a,b]))
    (h:∃ c,Sum.inl c ∈ ins):(simplify op m ins).1 = none:=by
  obtain ⟨c,hc⟩:=h
  rcases hok with ⟨rfl,a,rfl⟩ | ⟨hop,a,b,rfl⟩
  · simp at hc; subst hc; rfl
  · simp at hc
    rcases hop with rfl | rfl <;> rcases hc with rfl | rfl <;> (try cases a) <;> (try cases b) <;> rfl
theorem simplify_sound (op:GateOp) (hok:op = GateOp.and \/ op = GateOp.or \/ op = GateOp.not)
    (w:List Bool) (ins:List Stat) (hlen:ins.length ≤ 2)
    (hv:∀ s ∈ ins,statValid w.length s) :
    let r:=simplify op w.length ins
    statValid (w.length + r.1.toList.length) r.2 /\
    statVal (wiresFrom r.1.toList w) r.2 = op.eval (ins.map (statVal w)):=by
  rcases hok with rfl | rfl | rfl
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> simp at hlen
    · simp [simplify,simpAnd,statValid,statVal,GateOp.eval]
    · cases a with
      | inl c => simp [simplify,simpAnd,statValid,statVal,GateOp.eval]
      | inr j =>
        have hj:j < w.length:=hv (Sum.inr j) (by simp)
        simp [simplify,simpAnd,statValid,statVal,GateOp.eval,wiresFrom,hj]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp [simplify,simpAnd,statValid,statVal,GateOp.eval]
        | inr k =>
          have hk:k < w.length:=hv (Sum.inr k) (by simp)
          cases c <;> simp [simplify,simpAnd,statValid,statVal,GateOp.eval,wiresFrom,hk]
      | inr j =>
        cases b with
        | inl d =>
          have hj:j < w.length:=hv (Sum.inr j) (by simp)
          cases d <;> simp [simplify,simpAnd,statValid,statVal,GateOp.eval,wiresFrom,hj]
        | inr k =>
          simp [simplify,simpAnd,statValid,statVal,GateOp.eval,wiresFrom]
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> simp at hlen
    · simp [simplify,simpOr,statValid,statVal,GateOp.eval]
    · cases a with
      | inl c => simp [simplify,simpOr,statValid,statVal,GateOp.eval]
      | inr j =>
        have hj:j < w.length:=hv (Sum.inr j) (by simp)
        simp [simplify,simpOr,statValid,statVal,GateOp.eval,wiresFrom,hj]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp [simplify,simpOr,statValid,statVal,GateOp.eval]
        | inr k =>
          have hk:k < w.length:=hv (Sum.inr k) (by simp)
          cases c <;> simp [simplify,simpOr,statValid,statVal,GateOp.eval,wiresFrom,hk]
      | inr j =>
        cases b with
        | inl d =>
          have hj:j < w.length:=hv (Sum.inr j) (by simp)
          cases d <;> simp [simplify,simpOr,statValid,statVal,GateOp.eval,wiresFrom,hj]
        | inr k =>
          simp [simplify,simpOr,statValid,statVal,GateOp.eval,wiresFrom]
  · rcases ins with _ | ⟨a,l⟩
    · simp [simplify,simpNot,statValid,statVal,GateOp.eval]
    · cases a with
      | inl c => simp [simplify,simpNot,statValid,statVal,GateOp.eval]
      | inr j =>
        simp [simplify,simpNot,statValid,statVal,GateOp.eval,wiresFrom]
def elimStep (m:ℕ) (acc:List Stat × List Gate) (g:Gate):List Stat × List Gate :=
  let r:=simplify g.op (m + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2],acc.2 ++ r.1.toList)
def elim (m:ℕ) (gs:List Gate) (acc:List Stat × List Gate):List Stat × List Gate :=
  gs.foldl (elimStep m) acc
def Inv (m:ℕ) (w0 w:List Bool) (acc:List Stat × List Gate):Prop :=
  acc.1.length = w.length /\
  ∀ i,statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) /\
       statVal (wiresFrom acc.2 w0) (acc.1.getD i (Sum.inl false)) = w.getD i false
theorem inv_elimStep (m:ℕ) (w0 w:List Bool) (hw0:w0.length = m)
    (acc:List Stat × List Gate) (g:Gate) (hok:Ok g) (hi:Inv m w0 w acc) :
    Inv m w0 (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep m acc g):=by
  obtain ⟨hlen,hget⟩:=hi
  set ins:=g.inputs.map fun i => acc.1.getD i (Sum.inl false)
  set w':=wiresFrom acc.2 w0
  have hwl:w'.length = m + acc.2.length:=by rw [length_wiresFrom,hw0]
  have hs:=simplify_sound g.op hok.1 w' ins (by simpa [ins] using hok.2) (by
    intro s hs; obtain ⟨i,_,rfl⟩:=List.mem_map.1 hs; rw [hwl]; exact (hget i).1)
  simp only [hwl] at hs
  refine ⟨by simp [elimStep,hlen],fun i => ?_⟩
  simp only [elimStep]
  rw [List.length_append,<- Nat.add_assoc,wiresFrom_append]
  by_cases hiw:i = w.length
  · subst hiw
    rw [getD_snoc_len _ _ _ _ hlen,getD_snoc_eq]
    refine ⟨hs.1,?_⟩
    rw [hs.2]
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro j _
    exact (hget j).2
  · rw [getD_snoc_ne _ _ _ _ (by omega),getD_snoc_ne _ _ _ _ hiw]
    refine ⟨statValid_mono (by omega) _ (hget i).1,?_⟩
    have hv:=(hget i).1
    have he:=(hget i).2
    cases hst:acc.1.getD i (Sum.inl false) with
    | inl c =>
      rw [hst] at he
      exact he
    | inr j =>
      rw [hst] at hv he
      simp only [statValid,statVal] at hv he ⊢
      rw [getD_wiresFrom _ _ _ (by rw [hwl]; exact hv)]
      exact he
theorem inv_elim (m:ℕ) (w0:List Bool) (hw0:w0.length = m) (gs:List Gate) :
    ∀ w acc,(∀ g ∈ gs,Ok g) -> Inv m w0 w acc -> Inv m w0 (wiresFrom gs w) (elim m gs acc):=by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv
    exact ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (inv_elimStep m w0 w hw0 acc g (hok g List.mem_cons_self) hinv)
theorem elim_clean (m:ℕ) (gs:List Gate) :
    ∀ acc,(∀ g ∈ gs,Ok g) ->
      (∀ i,statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false))) ->
      CleanL m acc.2 -> CleanL m (elim m gs acc).2:=by
  induction gs with
  | nil => intro acc _ _ hc; exact hc
  | cons g gs ih =>
    intro acc hok hv hc
    apply ih _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    · intro i
      set ins:=g.inputs.map fun i => acc.1.getD i (Sum.inl false)
      have hs:=simplify_sound g.op (hok g List.mem_cons_self).1
        (List.replicate (m + acc.2.length) false) ins
        (by simpa [ins] using (hok g List.mem_cons_self).2)
        (by intro s hs; obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs; simpa using hv a)
      simp only [List.length_replicate] at hs
      simp only [elimStep]
      rw [List.length_append,<- Nat.add_assoc]
      by_cases hil:i = acc.1.length
      · subst hil; rw [getD_snoc_eq]; exact hs.1
      · rw [getD_snoc_ne _ _ _ _ hil]; exact statValid_mono (by omega) _ (hv i)
    · intro p g' hp
      simp only [elimStep] at hp
      by_cases hlt:p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp; exact hc p g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        set r:=simplify g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
        cases ho:r.1 with
        | none => simp [ho] at hp
        | some g0 =>
          rw [ho] at hp
          have hp0:p - acc.2.length = 0:=by
            have:=(List.getElem?_eq_some_iff.1 hp).1; simp at this; omega
          have hpeq:p = acc.2.length:=by omega
          rw [hp0] at hp; simp at hp; subst hp; rw [hpeq]
          exact simplify_clean g.op (m + acc.2.length) _ (by
            intro s hs; obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs; exact hv a) g0 (by rw [<- hr,ho]; rfl)
def isNotOp:GateOp -> Bool
  | GateOp.not => true
  | _ => false
def countNot (gs:List Gate):ℕ:=(gs.filter fun g => isNotOp g.op).length
theorem elim_len_and_not (m:ℕ) (gs:List Gate) :
    ∀ acc,(elim m gs acc).2.length ≤ acc.2.length + gs.length /\
           countNot (elim m gs acc).2 ≤ countNot acc.2 + countNot gs:=by
  induction gs with
  | nil => intro acc; simp [elim,countNot]
  | cons g gs ih =>
    intro acc
    have h1:=ih (elimStep m acc g)
    set r:=simplify g.op (m + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
    have hlen:(elimStep m acc g).2.length ≤ acc.2.length + 1:=by
      simp only [elimStep,List.length_append]
      cases r.1 <;> simp
    have hnot:countNot (elimStep m acc g).2 ≤ countNot acc.2 + (if isNotOp g.op then 1 else 0):=by
      simp only [elimStep,countNot,List.filter_append,List.length_append]
      cases ho:r.1 with
      | none => simp
      | some g0 =>
        have hg0:g0.op = g.op:=simplify_op g.op _ _ g0 (by rw [ho]; rfl)
        cases hnop:isNotOp g.op <;> simp [hg0,hnop]
    have hcgs:countNot (g :: gs) = (if isNotOp g.op then 1 else 0) + countNot gs:=by
      simp only [countNot,List.filter_cons]
      cases isNotOp g.op <;> simp [Nat.add_comm]
    change (elim m gs (elimStep m acc g)).2.length ≤ acc.2.length + (gs.length + 1) /\
           countNot (elim m gs (elimStep m acc g)).2 ≤ countNot acc.2 + countNot (g :: gs)
    constructor <;> omega
structure SGate where
  op:ℕ
  a:ℕ
  b:ℕ
deriving DecidableEq,Repr
def sOpEval (op:ℕ) (x y:Bool):Bool :=
  match op with
  | 0 => x && y
  | 1 => x || y
  | 2 => x && !y
  | _ => !x && y
def sWiresFrom (sgs:List SGate) (w:List Bool):List Bool :=
  sgs.foldl (fun w g => w ++ [sOpEval g.op (w.getD g.a false) (w.getD g.b false)]) w
theorem sWiresFrom_append (s1 s2:List SGate) (w:List Bool) :
    sWiresFrom (s1 ++ s2) w = sWiresFrom s2 (sWiresFrom s1 w):=by
  simp [sWiresFrom,List.foldl_append]
theorem sWiresFrom_prefix (sgs:List SGate):∀ w:List Bool,
    ∃ t:List Bool,sWiresFrom sgs w = w ++ t /\ t.length = sgs.length:=by
  induction sgs with
  | nil => intro w; exact ⟨[],by simp [sWiresFrom],rfl⟩
  | cons g sgs ih =>
    intro w
    obtain ⟨t,ht,hl⟩:=ih (w ++ [sOpEval g.op (w.getD g.a false) (w.getD g.b false)])
    refine ⟨sOpEval g.op (w.getD g.a false) (w.getD g.b false) :: t,?_,by simp [hl]⟩
    change sWiresFrom sgs (w ++ [sOpEval g.op (w.getD g.a false) (w.getD g.b false)]) = _
    rw [ht]; simp
theorem length_sWiresFrom (sgs:List SGate) (w:List Bool) :
    (sWiresFrom sgs w).length = w.length + sgs.length:=by
  obtain ⟨t,ht,hl⟩:=sWiresFrom_prefix sgs w
  rw [ht]; simp [hl]
theorem getD_sWiresFrom (sgs:List SGate) (w:List Bool) (i:ℕ) (h:i < w.length) :
    (sWiresFrom sgs w).getD i false = w.getD i false:=by
  obtain ⟨t,ht,_⟩:=sWiresFrom_prefix sgs w
  rw [ht,List.getD_append _ _ _ _ h]
def SCleanL (n:ℕ) (sgs:List SGate):Prop :=
  ∀ p g,sgs[p]? = some g -> g.a < n + p /\ g.b < n + p /\ g.op < 4
def stripAnd (pa pb:Bool):ℕ × Bool :=
  match pa,pb with
  | false,false => (0,false)
  | false,true  => (2,false)
  | true, false => (3,false)
  | true, true  => (1,true)
def stripOr (pa pb:Bool):ℕ × Bool :=
  match pa,pb with
  | false,false => (1,false)
  | false,true  => (3,true)
  | true, false => (2,true)
  | true, true  => (0,true)
def stripStep (n:ℕ) (acc:List (ℕ × Bool) × List SGate) (g:Gate) :
    List (ℕ × Bool) × List SGate :=
  match g.op,g.inputs with
  | GateOp.not,[j] =>
    let p:=acc.1.getD j (0,false)
    (acc.1 ++ [(p.1,!p.2)],acc.2)
  | GateOp.and,[j,k] =>
    let pj:=acc.1.getD j (0,false)
    let pk:=acc.1.getD k (0,false)
    let (op,pol):=stripAnd pj.2 pk.2
    (acc.1 ++ [(n + acc.2.length,pol)],acc.2 ++ [⟨op,pj.1,pk.1⟩])
  | GateOp.or,[j,k] =>
    let pj:=acc.1.getD j (0,false)
    let pk:=acc.1.getD k (0,false)
    let (op,pol):=stripOr pj.2 pk.2
    (acc.1 ++ [(n + acc.2.length,pol)],acc.2 ++ [⟨op,pj.1,pk.1⟩])
  | _,_ => (acc.1 ++ [(0,false)],acc.2)
def stripNot (n:ℕ) (gs:List Gate):List (ℕ × Bool) × List SGate :=
  gs.foldl (stripStep n) (List.ofFn (fun i:Fin n => (i.val,false)),[])
theorem stripNot_sound (n:ℕ) (gs:List Gate) (hcl:CleanL n gs) :
    let res:=stripNot n gs
    SCleanL n res.2 /\
    res.2.length + countNot gs = gs.length /\
    res.1.length = n + gs.length /\
    (∀ i,i < n + gs.length -> (res.1.getD i (0,false)).1 < n + res.2.length) /\
    (∀ (x:Fin n -> Bool) (i:ℕ),i < n + gs.length ->
      let p:=res.1.getD i (0,false)
      xor ((sWiresFrom res.2 (List.ofFn x)).getD p.1 false) p.2 =
        (wiresFrom gs (List.ofFn x)).getD i false):=by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨fun p g hp => by simp [stripNot] at hp,by simp [stripNot,countNot],by simp [stripNot],?_,?_⟩
    · intro i hi
      have hi':i < n:=by simpa using hi
      simp [stripNot,hi']
    · intro x i hi
      have hi':i < n:=by simpa using hi
      simp [stripNot,sWiresFrom,wiresFrom,hi']
  | append_singleton gs g ih =>
    have hcl_pre:CleanL n gs:=fun p g' hp => by
      have hlt:p < gs.length:=(List.getElem?_eq_some_iff.1 hp).1
      exact hcl p g' (by rw [List.getElem?_append_left hlt]; exact hp)
    have hcl_g:CleanG (n + gs.length) g:=hcl gs.length g (by simp)
    obtain ⟨hsc,hlen,hrlen,hbd,hev⟩:=ih hcl_pre
    have hres:stripNot n (gs ++ [g]) = stripStep n (stripNot n gs) g:=by
      simp [stripNot,List.foldl_append]
    rw [hres]
    set acc:=stripNot n gs
    rcases hcl_g with ⟨hop,j,hj,hinp⟩ | ⟨hop,j,k,hj,hk,hinp⟩
    · have hstep:stripStep n acc g = (acc.1 ++ [((acc.1.getD j (0,false)).1,!(acc.1.getD j (0,false)).2)],acc.2):=by
        simp [stripStep,hop,hinp]
      rw [hstep]
      refine ⟨hsc,?_,by simp [hrlen]; omega,?_,?_⟩
      · have hcn:countNot (gs ++ [g]) = countNot gs + 1:=by
          simp [countNot,List.filter_append,hop,isNotOp]
        rw [hcn]; simp; omega
      · intro i hi
        have hi_le:i ≤ n + gs.length:=by simp at hi; omega
        by_cases hil:i = n + gs.length
        · subst hil; rw [getD_snoc_len _ _ _ _ hrlen]; exact hbd j hj
        · rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hbd i (by omega)
      · intro x i hi
        have hi_le:i ≤ n + gs.length:=by simp at hi; omega
        rw [wiresFrom_append]
        have hwl:(wiresFrom gs (List.ofFn x)).length = n + gs.length:=by
          rw [length_wiresFrom]; simp
        by_cases hil:i = n + gs.length
        · subst hil
          rw [getD_snoc_len _ _ _ _ hrlen]
          change xor ((sWiresFrom acc.2 (List.ofFn x)).getD (acc.1.getD j (0,false)).1 false)
              (!(acc.1.getD j (0,false)).2) =
            (wiresFrom gs (List.ofFn x) ++ [g.op.eval (g.inputs.map fun a => (wiresFrom gs (List.ofFn x)).getD a false)]).getD (n + gs.length) false
          rw [getD_snoc_len _ _ _ _ hwl,hop,hinp]
          simp only [List.map_cons,List.map_nil,GateOp.eval]
          rw [<- hev x j hj]
          cases ((sWiresFrom acc.2 (List.ofFn x)).getD (acc.1.getD j (0,false)).1 false) <;>
          cases (acc.1.getD j (0,false)).2 <;> rfl
        · rw [getD_snoc_ne _ _ _ _ (by omega)]
          rw [getD_wiresFrom [g] _ i (by rw [hwl]; omega)]
          exact hev x i (by omega)
    · set pj:=acc.1.getD j (0,false)
      set pk:=acc.1.getD k (0,false)
      set pair:ℕ × Bool:=match g.op with
        | GateOp.and => stripAnd pj.2 pk.2
        | _ => stripOr pj.2 pk.2
      have hstep:stripStep n acc g = (acc.1 ++ [(n + acc.2.length,pair.2)],acc.2 ++ [⟨pair.1,pj.1,pk.1⟩]):=by
        rcases hop with hop | hop <;> simp [stripStep,hop,hinp,pair,pj,pk]
      rw [hstep]
      have hpair_lt:pair.1 < 4:=by
        rcases hop with hop | hop <;> simp only [pair,hop]
        · cases pj.2 <;> cases pk.2 <;> decide
        · cases pj.2 <;> cases pk.2 <;> decide
      have hnot_g:isNotOp g.op = false:=by rcases hop with h | h <;> simp [h,isNotOp]
      refine ⟨?_,?_,by simp [hrlen]; omega,?_,?_⟩
      · intro p g' hp
        by_cases hlt:p < acc.2.length
        · rw [List.getElem?_append_left hlt] at hp; exact hsc p g' hp
        · rw [List.getElem?_append_right (by omega)] at hp
          have hp0:p - acc.2.length = 0:=by
            have:=(List.getElem?_eq_some_iff.1 hp).1; simp at this; omega
          have hpeq:p = acc.2.length:=by omega
          rw [hp0] at hp; simp at hp; subst hp; rw [hpeq]
          exact ⟨hbd j hj,hbd k hk,hpair_lt⟩
      · have hcn:countNot (gs ++ [g]) = countNot gs:=by
          simp [countNot,List.filter_append,hnot_g]
        rw [hcn]; simp; omega
      · intro i hi
        have hi_le:i ≤ n + gs.length:=by simp at hi; omega
        by_cases hil:i = n + gs.length
        · subst hil; rw [getD_snoc_len _ _ _ _ hrlen]; simp
        · rw [getD_snoc_ne _ _ _ _ (by omega)]
          have h1:=hbd i (by omega)
          rw [List.length_append,List.length_singleton]; omega
      · intro x i hi
        have hi_le:i ≤ n + gs.length:=by simp at hi; omega
        rw [wiresFrom_append,sWiresFrom_append]
        have hwl:(wiresFrom gs (List.ofFn x)).length = n + gs.length:=by
          rw [length_wiresFrom]; simp
        have hswl:(sWiresFrom acc.2 (List.ofFn x)).length = n + acc.2.length:=by
          rw [length_sWiresFrom]; simp
        by_cases hil:i = n + gs.length
        · subst hil
          rw [getD_snoc_len _ _ _ _ hrlen]
          change xor ((sWiresFrom acc.2 (List.ofFn x) ++ [sOpEval pair.1 ((sWiresFrom acc.2 (List.ofFn x)).getD pj.1 false) ((sWiresFrom acc.2 (List.ofFn x)).getD pk.1 false)]).getD (n + acc.2.length) false) pair.2 =
            (wiresFrom gs (List.ofFn x) ++ [g.op.eval (g.inputs.map fun a => (wiresFrom gs (List.ofFn x)).getD a false)]).getD (n + gs.length) false
          rw [getD_snoc_len _ _ _ _ hswl,getD_snoc_len _ _ _ _ hwl,hinp]
          simp only [List.map_cons,List.map_nil]
          rw [<- hev x j hj,<- hev x k hk]
          rcases hop with hop | hop <;> simp only [pair,hop,GateOp.eval]
          · cases ((sWiresFrom acc.2 (List.ofFn x)).getD pj.1 false) <;>
            cases ((sWiresFrom acc.2 (List.ofFn x)).getD pk.1 false) <;>
            cases pj.2 <;> cases pk.2 <;> rfl
          · cases ((sWiresFrom acc.2 (List.ofFn x)).getD pj.1 false) <;>
            cases ((sWiresFrom acc.2 (List.ofFn x)).getD pk.1 false) <;>
            cases pj.2 <;> cases pk.2 <;> rfl
        · rw [getD_snoc_ne _ _ _ _ (by omega)]
          dsimp only
          rw [getD_wiresFrom [g] _ i (by rw [hwl]; omega)]
          rw [getD_sWiresFrom _ _ _ (by rw [hswl]; exact hbd i (by omega))]
          exact hev x i (by omega)
end PEqualNP.Outside.L_meta_10650_aux
namespace PEqualNP.Outside.L_meta_10650_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def Reach (n:ℕ) (gs:List Gate) (o a:ℕ):Prop :=
  ∀ P:ℕ -> Prop,P o ->
    (∀ q g,gs[q]? = some g -> P (n + q) -> ∀ u ∈ g.inputs,P u) -> P a
theorem reach_self (n:ℕ) (gs:List Gate) (o:ℕ):Reach n gs o o :=
  fun _ ho _ => ho
theorem reach_step {n:ℕ} {gs:List Gate} {o q u:ℕ} {g:Gate}
    (hq:gs[q]? = some g) (hr:Reach n gs o (n + q)) (hu:u ∈ g.inputs) :
    Reach n gs o u :=
  fun P ho hs => hs q g hq (hr P ho hs) u hu
theorem reach_cases {n:ℕ} {gs:List Gate} {o a:ℕ} (h:Reach n gs o a) :
    a = o \/ ∃ q g,gs[q]? = some g /\ a ∈ g.inputs /\ Reach n gs o (n + q):=by
  apply h (fun x => x = o \/ ∃ q g,gs[q]? = some g /\ x ∈ g.inputs /\ Reach n gs o (n + q))
  · exact Or.inl rfl
  · intro q g hq hP u hu
    refine Or.inr ⟨q,g,hq,hu,?_⟩
    rcases hP with rfl | ⟨q',g',hq',hin',hr'⟩
    · exact reach_self n gs (n + q)
    · exact reach_step hq' hr' hin'
theorem split_at {α:Type} (gs:List α) (p:ℕ) (g:α) (hp:gs[p]? = some g) :
    ∃ pre post,gs = pre ++ g :: post /\ pre.length = p:=by
  have hlt:p < gs.length:=(List.getElem?_eq_some_iff.1 hp).1
  have hget:gs[p] = g:=(List.getElem?_eq_some_iff.1 hp).2
  refine ⟨gs.take p,gs.drop (p + 1),?_,by simp; omega⟩
  have h1:gs = gs.take p ++ gs.drop p:=(List.take_append_drop p gs).symm
  have h2:gs.drop p = gs[p] :: gs.drop (p + 1):=List.drop_eq_getElem_cons hlt
  exact h1.trans (by rw [h2,hget])
theorem wiresFrom_getD_gate (n:ℕ) (gs:List Gate) (p:ℕ) (g:Gate) (hp:gs[p]? = some g)
    (hlt:∀ a ∈ g.inputs,a < n + p) (w:List Bool) (hw:w.length = n) :
    (wiresFrom gs w).getD (n + p) false =
      g.op.eval (g.inputs.map fun a => (wiresFrom gs w).getD a false):=by
  obtain ⟨pre,post,rfl,hlen⟩:=split_at gs p g hp
  have h1:wiresFrom (pre ++ g :: post) w = wiresFrom post
      (wiresFrom pre w ++ [g.op.eval (g.inputs.map fun i => (wiresFrom pre w).getD i false)]):=by
    rw [wiresFrom_append]; rfl
  have hl:(wiresFrom pre w).length = n + p:=by rw [length_wiresFrom,hw,hlen]
  rw [h1,getD_wiresFrom _ _ _ (by simp [hl]),getD_snoc_len _ _ _ _ hl]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hal:=hlt a ha
  rw [getD_wiresFrom post _ a (by simp [hl]; omega),List.getD_append _ _ _ _ (by omega)]
theorem set_dead_eval (n:ℕ) (gs:List Gate) (o p:ℕ) (gnew:Gate)
    (hcl:CleanL n gs) (ho:o < n + gs.length) (hnr:¬ Reach n gs o (n + p))
    (w:List Bool) (hw:w.length = n) :
    (wiresFrom (gs.set p gnew) w).getD o false = (wiresFrom gs w).getD o false:=by
  have key:∀ a,a < n + gs.length -> Reach n gs o a ->
      (wiresFrom (gs.set p gnew) w).getD a false = (wiresFrom gs w).getD a false:=by
    intro a
    induction a using Nat.strong_induction_on with
    | ind a ih =>
      intro ha hra
      by_cases hlt:a < n
      · rw [getD_wiresFrom _ _ _ (by omega),getD_wiresFrom _ _ _ (by omega)]
      · have hqlt:a - n < gs.length:=by omega
        have haeq:a = n + (a - n):=by omega
        set q:=a - n
        have hq:gs[q]? = some gs[q]:=List.getElem?_eq_getElem hqlt
        have hne:q ≠ p:=by rintro rfl; exact hnr (haeq ▸ hra)
        have hq':(gs.set p gnew)[q]? = some gs[q]:=by
          rw [List.getElem?_set_ne (Ne.symm hne),hq]
        have hglt:∀ u ∈ gs[q].inputs,u < n + q:=cleanG_lt (hcl q gs[q] hq)
        rw [haeq,wiresFrom_getD_gate n (gs.set p gnew) q gs[q] hq' hglt w hw,
            wiresFrom_getD_gate n gs q gs[q] hq hglt w hw]
        congr 1
        apply List.map_congr_left
        intro u hu
        have hul:=hglt u hu
        exact ih u (by omega) (by omega) (reach_step hq (haeq ▸ hra) hu)
  exact key o ho (reach_self n gs o)
theorem eval_indep_of_unread (n:ℕ) (gs:List Gate) (hcl:CleanL n gs) (i:ℕ)
    (hno:∀ (p:ℕ) (g:Gate),gs[p]? = some g -> i ∉ g.inputs)
    (w1 w2:List Bool) (hw1:w1.length = n) (hw2:w2.length = n)
    (heq:∀ j,j ≠ i -> w1.getD j false = w2.getD j false) :
    ∀ a,a < n + gs.length -> a ≠ i ->
      (wiresFrom gs w1).getD a false = (wiresFrom gs w2).getD a false:=by
  intro a
  induction a using Nat.strong_induction_on with
  | ind a ih =>
    intro ha hne
    by_cases hlt:a < n
    · rw [getD_wiresFrom _ _ _ (by omega),getD_wiresFrom _ _ _ (by omega)]
      exact heq a hne
    · have hqlt:a - n < gs.length:=by omega
      have haeq:a = n + (a - n):=by omega
      set q:=a - n
      have hq:gs[q]? = some gs[q]:=List.getElem?_eq_getElem hqlt
      have hglt:∀ u ∈ gs[q].inputs,u < n + q:=cleanG_lt (hcl q gs[q] hq)
      rw [haeq,wiresFrom_getD_gate n gs q gs[q] hq hglt w1 hw1,
          wiresFrom_getD_gate n gs q gs[q] hq hglt w2 hw2]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hul:=hglt u hu
      have hui:u ≠ i:=fun h => hno q gs[q] hq (h ▸ hu)
      exact ih u (by omega) (by omega) hui
theorem elim_stat_prefix (m:ℕ) (gs:List Gate) :
    ∀ acc,∃ t,(elim m gs acc).1 = acc.1 ++ t /\ t.length = gs.length:=by
  induction gs with
  | nil => intro acc; exact ⟨[],by simp [elim],rfl⟩
  | cons g gs ih =>
    intro acc
    obtain ⟨t,ht,hl⟩:=ih (elimStep m acc g)
    refine ⟨(simplify g.op (m + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 :: t,?_,by simp [hl]⟩
    change (elim m gs (elimStep m acc g)).1 = _
    rw [ht]; simp [elimStep]
theorem elim_stat_getD_lt (m:ℕ) (gs:List Gate) (acc:List Stat × List Gate)
    (i:ℕ) (h:i < acc.1.length) :
    (elim m gs acc).1.getD i (Sum.inl false) = acc.1.getD i (Sum.inl false):=by
  obtain ⟨t,ht,_⟩:=elim_stat_prefix m gs acc
  rw [ht,List.getD_append _ _ _ _ h]
theorem elim_len_split (m:ℕ) (gs1 gs2:List Gate) (acc:List Stat × List Gate) :
    elim m (gs1 ++ gs2) acc = elim m gs2 (elim m gs1 acc):=by
  simp [elim,List.foldl_append]
theorem elim_drop_at (m:ℕ) (gs:List Gate) (acc:List Stat × List Gate) (p:ℕ) (g:Gate)
    (hp:gs[p]? = some g)
    (hdrop:(simplify g.op (m + (elim m (gs.take p) acc).2.length)
      (g.inputs.map fun i => (elim m (gs.take p) acc).1.getD i (Sum.inl false))).1 = none) :
    (elim m gs acc).2.length + 1 ≤ acc.2.length + gs.length:=by
  obtain ⟨pre,post,hgs,hplen⟩:=split_at gs p g hp
  have htake:gs.take p = pre:=by rw [hgs,List.take_left' hplen]
  rw [htake] at hdrop
  rw [hgs,elim_len_split]
  set acc1:=elim m pre acc
  have h1:acc1.2.length ≤ acc.2.length + pre.length:=(elim_len_and_not m pre acc).1
  have hstep:(elimStep m acc1 g).2 = acc1.2:=by dsimp only [elimStep]; rw [hdrop]; simp
  have h2:=(elim_len_and_not m post (elimStep m acc1 g)).1
  rw [hstep] at h2
  change (elim m post (elimStep m acc1 g)).2.length + 1 ≤ acc.2.length + (pre ++ g :: post).length
  simp only [List.length_append,List.length_cons]
  omega
theorem elim_drop_at_two (m:ℕ) (gs:List Gate) (acc:List Stat × List Gate)
    (p q:ℕ) (gp gq:Gate) (hpq:p < q) (hp:gs[p]? = some gp) (hq:gs[q]? = some gq)
    (hdp:(simplify gp.op (m + (elim m (gs.take p) acc).2.length)
      (gp.inputs.map fun i => (elim m (gs.take p) acc).1.getD i (Sum.inl false))).1 = none)
    (hdq:(simplify gq.op (m + (elim m (gs.take q) acc).2.length)
      (gq.inputs.map fun i => (elim m (gs.take q) acc).1.getD i (Sum.inl false))).1 = none) :
    (elim m gs acc).2.length + 2 ≤ acc.2.length + gs.length:=by
  obtain ⟨pre,post,hgs,hplen⟩:=split_at gs p gp hp
  have htakeP:gs.take p = pre:=by rw [hgs,List.take_left' hplen]
  rw [htakeP] at hdp
  have hq_post:post[q - (p + 1)]? = some gq:=by
    rw [hgs,List.getElem?_append_right (by omega)] at hq
    have:q - pre.length = (q - (p + 1)) + 1:=by omega
    rw [this] at hq
    simpa using hq
  obtain ⟨mid,suf,hpost,hmlen⟩:=split_at post (q - (p + 1)) gq hq_post
  have hgs2:gs = pre ++ gp :: (mid ++ gq :: suf):=by rw [hgs,hpost]
  have htakeQ:gs.take q = pre ++ gp :: mid:=by
    rw [hgs2]
    have h1:(pre ++ gp :: mid) ++ gq :: suf = pre ++ gp :: (mid ++ gq :: suf):=by simp
    rw [<- h1,List.take_left' (by simp; omega)]
  rw [htakeQ] at hdq
  rw [hgs2,elim_len_split]
  set acc1:=elim m pre acc
  have h1:acc1.2.length ≤ acc.2.length + pre.length:=(elim_len_and_not m pre acc).1
  have hstep1:(elimStep m acc1 gp).2 = acc1.2:=by dsimp only [elimStep]; rw [hdp]; simp
  have hmid:elim m (gp :: (mid ++ gq :: suf)) acc1 = elim m (gq :: suf) (elim m mid (elimStep m acc1 gp)):=by
    change elim m (mid ++ gq :: suf) (elimStep m acc1 gp) = _
    rw [elim_len_split]
  rw [hmid]
  set acc2:=elim m mid (elimStep m acc1 gp)
  have hacc2_eq:acc2 = elim m (pre ++ gp :: mid) acc:=by
    rw [elim_len_split]; rfl
  rw [<- hacc2_eq] at hdq
  have h2:acc2.2.length ≤ acc1.2.length + mid.length:=by
    have:=(elim_len_and_not m mid (elimStep m acc1 gp)).1
    rwa [hstep1] at this
  have hstep2:(elimStep m acc2 gq).2 = acc2.2:=by dsimp only [elimStep]; rw [hdq]; simp
  have h3:=(elim_len_and_not m suf (elimStep m acc2 gq)).1
  rw [hstep2] at h3
  change (elim m suf (elimStep m acc2 gq)).2.length + 2 ≤ acc.2.length + (pre ++ gp :: (mid ++ gq :: suf)).length
  simp only [List.length_append,List.length_cons]
  omega
theorem elim_gates_prefix (m:ℕ) (gs:List Gate) :
    ∀ acc,∃ t,(elim m gs acc).2 = acc.2 ++ t:=by
  induction gs with
  | nil => intro acc; exact ⟨[],by simp [elim]⟩
  | cons g gs ih =>
    intro acc
    obtain ⟨t,ht⟩:=ih (elimStep m acc g)
    refine ⟨(simplify g.op (m + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList ++ t,?_⟩
    change (elim m gs (elimStep m acc g)).2 = _
    rw [ht]; simp [elimStep,List.append_assoc]
theorem elim_not_dropped (m:ℕ) (gs:List Gate) (acc:List Stat × List Gate)
    (p:ℕ) (gp:Gate) (hp:gs[p]? = some gp) (hnot:gp.op = GateOp.not)
    (hzero:countNot (elim m gs acc).2 = 0) :
    (simplify gp.op (m + (elim m (gs.take p) acc).2.length)
      (gp.inputs.map fun i => (elim m (gs.take p) acc).1.getD i (Sum.inl false))).1 = none:=by
  obtain ⟨pre,post,hgs,hplen⟩:=split_at gs p gp hp
  have htake:gs.take p = pre:=by rw [hgs,List.take_left' hplen]
  rw [htake]
  set acc1:=elim m pre acc
  set r:=simplify gp.op (m + acc1.2.length) (gp.inputs.map fun i => acc1.1.getD i (Sum.inl false)) with hr_def
  cases hr:r.1 with
  | none => rfl
  | some g0 =>
    exfalso
    have hg0:g0.op = GateOp.not:=(simplify_op gp.op _ _ g0 (by rw [<- hr_def,hr]; rfl)).trans hnot
    have hstep:(elimStep m acc1 gp).2 = acc1.2 ++ [g0]:=by
      dsimp only [elimStep]; rw [<- hr_def,hr]; simp
    obtain ⟨t,ht⟩:=elim_gates_prefix m post (elimStep m acc1 gp)
    have htot:(elim m gs acc).2 = acc1.2 ++ [g0] ++ t:=by
      rw [hgs,elim_len_split]
      change (elim m post (elimStep m acc1 gp)).2 = _
      rw [ht,hstep]
    rw [htot] at hzero
    simp only [countNot,List.filter_append,List.filter_cons,List.filter_nil,
      List.length_append,hg0,isNotOp,↓reduceIte,List.length_cons,List.length_nil] at hzero
    omega
theorem elim_const_forces_drop (n:ℕ) (g:Gate) (hcl:CleanG n g)
    (st:List Stat) (next u:ℕ) (c:Bool)
    (hu:u ∈ g.inputs) (hc:st.getD u (Sum.inl false) = Sum.inl c) :
    (simplify g.op next (g.inputs.map fun i => st.getD i (Sum.inl false))).1 = none:=by
  rcases hcl with ⟨hop,a,_,hinp⟩ | ⟨hop,a,b,_,_,hinp⟩
  · rw [hinp] at hu ⊢
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
    subst hu
    simp only [hop,simplify,List.map_cons,List.map_nil,hc,simpNot]
  · rw [hinp] at hu ⊢
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl
    · rcases hop with hop | hop <;>
      · simp only [hop,simplify,List.map_cons,List.map_nil,hc]
        cases st.getD b (Sum.inl false) with
        | inl d => cases c <;> simp [simpAnd,simpOr]
        | inr k => cases c <;> simp [simpAnd,simpOr]
    · rcases hop with hop | hop <;>
      · simp only [hop,simplify,List.map_cons,List.map_nil,hc]
        cases st.getD a (Sum.inl false) with
        | inl d => cases d <;> cases c <;> simp [simpAnd,simpOr]
        | inr j => cases c <;> simp [simpAnd,simpOr]
theorem simplify_not_none_const (next:ℕ) (ins:List Stat)
    (h:(simplify GateOp.not next ins).1 = none) :
    ∃ c:Bool,(simplify GateOp.not next ins).2 = Sum.inl c:=by
  rcases ins with _ | ⟨a,l⟩
  · exact ⟨true,rfl⟩
  · cases a with
    | inl c => exact ⟨!c,rfl⟩
    | inr j => simp [simplify,simpNot] at h
theorem cleanL_ok {n:ℕ} {gs:List Gate} (hcl:CleanL n gs):∀ g ∈ gs,Ok g:=by
  intro g hg
  obtain ⟨p,hp,rfl⟩:=List.getElem_of_mem hg
  rcases hcl p gs[p] (List.getElem?_eq_getElem hp) with ⟨hop,a,_,hinp⟩ | ⟨hop,a,b,_,_,hinp⟩
  · exact ⟨Or.inr (Or.inr hop),by simp [hinp]⟩
  · exact ⟨hop.elim Or.inl (Or.inr ∘ Or.inl),by simp [hinp]⟩
theorem circuit_eval_eq (gs:List Gate) (o:ℕ) (w:List Bool) :
    Circuit.eval ⟨gs,o⟩ w = (wiresFrom gs w).getD o false:=rfl
theorem countNot_le_one_of_unique (gs:List Gate)
    (huniq:∀ i j:Fin gs.length,(gs.get i).op = GateOp.not -> (gs.get j).op = GateOp.not -> i = j) :
    countNot gs ≤ 1:=by
  induction gs with
  | nil => simp [countNot]
  | cons g gs ih =>
    have hsub:∀ i j:Fin gs.length,(gs.get i).op = GateOp.not -> (gs.get j).op = GateOp.not -> i = j:=by
      intro i j hi hj
      have h:=huniq i.succ j.succ hi hj
      exact Fin.succ_inj.1 h
    cases hgop:g.op with
    | not =>
      have hrest:countNot gs = 0:=by
        simp only [countNot,List.length_eq_zero_iff,List.filter_eq_nil_iff]
        intro g' hg'
        obtain ⟨k,rfl⟩:=List.get_of_mem hg'
        cases hkop:(gs.get k).op <;> simp [isNotOp]
        have h:=huniq ⟨0,by simp⟩ k.succ hgop hkop
        exact absurd (congrArg Fin.val h) (by simp)
      simp only [countNot,List.filter_cons,hgop,isNotOp,↓reduceIte,List.length_cons]
      change (gs.filter fun g => isNotOp g.op).length + 1 ≤ 1
      change (gs.filter fun g => isNotOp g.op).length = 0 at hrest
      omega
    | and =>
      simp only [countNot,List.filter_cons,hgop,isNotOp,Bool.false_eq_true,↓reduceIte]
      exact ih hsub
    | or =>
      simp only [countNot,List.filter_cons,hgop,isNotOp,Bool.false_eq_true,↓reduceIte]
      exact ih hsub
    | _ =>
      simp only [countNot,List.filter_cons,hgop,isNotOp,Bool.false_eq_true,↓reduceIte]
      exact ih hsub
theorem no_not_of_countNot_zero (gs:List Gate)
    (hok:∀ g ∈ gs,Ok g) (hz:countNot gs = 0) :
    ∀ g ∈ gs,(g.op = GateOp.and \/ g.op = GateOp.or) /\ g.inputs.length ≤ 2:=by
  intro g hg
  refine ⟨?_,(hok g hg).2⟩
  rcases (hok g hg).1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    simp only [countNot,List.length_eq_zero_iff,List.filter_eq_nil_iff] at hz
    have:=hz g hg
    simp [h,isNotOp] at this
theorem exists_unique_not_of_countNot_one (gs:List Gate) (h1:countNot gs = 1) :
    ∃ p gp,gs[p]? = some gp /\ gp.op = GateOp.not /\
      countNot (gs.set p ⟨GateOp.and,[0,0]⟩) = 0:=by
  induction gs with
  | nil => simp [countNot] at h1
  | cons g gs ih =>
    cases hgop:g.op with
    | not =>
      have hrest:countNot gs = 0:=by
        simp only [countNot,List.filter_cons,hgop,isNotOp,↓reduceIte,List.length_cons] at h1
        change (gs.filter fun g => isNotOp g.op).length = 0
        have h1':(gs.filter fun g => isNotOp g.op).length + 1 = 1:=h1
        omega
      refine ⟨0,g,rfl,hgop,?_⟩
      simp only [List.set_cons_zero,countNot,List.filter_cons,isNotOp,Bool.false_eq_true,↓reduceIte]
      exact hrest
    | and =>
      simp only [countNot,List.filter_cons,hgop,isNotOp,Bool.false_eq_true,↓reduceIte] at h1
      obtain ⟨p,gp,hp,hnot,hset⟩:=ih h1
      refine ⟨p + 1,gp,hp,hnot,?_⟩
      simp only [List.set_cons_succ,countNot,List.filter_cons,hgop,isNotOp,Bool.false_eq_true,↓reduceIte]
      exact hset
    | or =>
      simp only [countNot,List.filter_cons,hgop,isNotOp,Bool.false_eq_true,↓reduceIte] at h1
      obtain ⟨p,gp,hp,hnot,hset⟩:=ih h1
      refine ⟨p + 1,gp,hp,hnot,?_⟩
      simp only [List.set_cons_succ,countNot,List.filter_cons,hgop,isNotOp,Bool.false_eq_true,↓reduceIte]
      exact hset
    | _ =>
      simp only [countNot,List.filter_cons,hgop,isNotOp,Bool.false_eq_true,↓reduceIte] at h1
      obtain ⟨p,gp,hp,hnot,hset⟩:=ih h1
      refine ⟨p + 1,gp,hp,hnot,?_⟩
      simp only [List.set_cons_succ,countNot,List.filter_cons,hgop,isNotOp,Bool.false_eq_true,↓reduceIte]
      exact hset
def w13Gates:List Gate :=
  [ ⟨GateOp.or, [0,1]⟩,
    ⟨GateOp.or, [3,4]⟩,
    ⟨GateOp.or, [5,6]⟩,
    ⟨GateOp.and,[7,8]⟩,
    ⟨GateOp.or, [0,4]⟩,
    ⟨GateOp.or, [1,3]⟩,
    ⟨GateOp.and,[9,12]⟩,
    ⟨GateOp.or, [5,11]⟩,
    ⟨GateOp.or, [6,10]⟩,
    ⟨GateOp.and,[14,15]⟩,
    ⟨GateOp.or, [13,16]⟩,
    ⟨GateOp.and,[2,6]⟩,
    ⟨GateOp.or, [17,18]⟩ ]
def gEdgeList:List ℕ:=[0,3,0,4,1,4,1,5,3,5,0,6,1,6,2,6,3,6,4,6,5,6]
def evalG (x:Fin 7 -> Bool):Bool :=
  decide (∃ i < gEdgeList.length / 2,
    (List.ofFn x).getD (gEdgeList.getD (2 * i) 0) false = true /\
    (List.ofFn x).getD (gEdgeList.getD (2 * i + 1) 0) false = true)
def evalGBool (x0 x1 x2 x3 x4 x5 x6:Bool):Bool :=
  (x0 && x3) || (x0 && x4) || (x1 && x4) || (x1 && x5) || (x3 && x5) ||
  (x0 && x6) || (x1 && x6) || (x2 && x6) || (x3 && x6) || (x4 && x6) || (x5 && x6)
theorem w13_ok:∀ g ∈ w13Gates,(g.op = GateOp.and \/ g.op = GateOp.or) /\ g.inputs.length ≤ 2:=by
  intro g hg
  simp only [w13Gates,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by simp,by decide⟩
theorem w13_len:w13Gates.length = 13:=rfl
theorem evalG_eq_bool (x:Fin 7 -> Bool) :
    evalG x = evalGBool (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6):=by
  cases h0:x 0 <;> cases h1:x 1 <;> cases h2:x 2 <;> cases h3:x 3 <;>
  cases h4:x 4 <;> cases h5:x 5 <;> cases h6:x 6 <;>
  · have hfn:List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6]:=by
      simp [List.ofFn_succ]
    simp only [evalG,hfn,h0,h1,h2,h3,h4,h5,h6]
    decide
theorem w13_eval (x:Fin 7 -> Bool) :
    Circuit.eval ⟨w13Gates,19⟩ (List.ofFn x) = evalG x:=by
  rw [evalG_eq_bool]
  have hfn:List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6]:=by
    simp [List.ofFn_succ]
  rw [hfn]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;>
  cases x 4 <;> cases x 5 <;> cases x 6 <;> rfl
def evalW5 (y:Fin 6 -> Bool):Bool :=
  (y 0 && y 2) || (y 0 && y 3) || (y 1 && y 3) || (y 1 && y 4) || (y 2 && y 4) ||
  (y 0 && y 5) || (y 1 && y 5) || (y 2 && y 5) || (y 3 && y 5) || (y 4 && y 5)
def liftW5 (y:Fin 6 -> Bool):Fin 7 -> Bool:=fun i =>
  match i.val with
  | 0 => y 0
  | 1 => y 1
  | 2 => false
  | 3 => y 2
  | 4 => y 3
  | 5 => y 4
  | _ => y 5
theorem evalG_liftW5 (y:Fin 6 -> Bool):evalG (liftW5 y) = evalW5 y:=by
  rw [evalG_eq_bool]
  simp [liftW5,evalGBool,evalW5]
def sub2Init:List Stat :=
  [Sum.inr 0,Sum.inr 1,Sum.inl false,Sum.inr 2,Sum.inr 3,Sum.inr 4,Sum.inr 5]
theorem reduce_G_to_W5
    (hW5:∀ (sgs:List SGate) (o:ℕ) (pol:Bool),
      SCleanL 6 sgs -> sgs.length ≤ 10 -> o < 6 + sgs.length ->
      ¬ ∀ y:Fin 6 -> Bool,xor ((sWiresFrom sgs (List.ofFn y)).getD o false) pol = evalW5 y) :
    ∀ (gates:List Gate) (o:ℕ),
      (∀ g ∈ gates,(g.op = GateOp.and \/ g.op = GateOp.or \/ g.op = GateOp.not) /\ g.inputs.length ≤ 2) ->
      (∀ i j:Fin gates.length,(gates.get i).op = GateOp.not -> (gates.get j).op = GateOp.not -> i = j) ->
      (∀ x:Fin 7 -> Bool,Circuit.eval ⟨gates,o⟩ (List.ofFn x) = evalG x) ->
      ∃ (gates':List Gate) (o':ℕ),
        (∀ g ∈ gates',(g.op = GateOp.and \/ g.op = GateOp.or) /\ g.inputs.length ≤ 2) /\
        gates'.length ≤ gates.length /\
        ∀ x:Fin 7 -> Bool,Circuit.eval ⟨gates',o'⟩ (List.ofFn x) = evalG x:=by
  intro gates o hok huniq heval
  set init7:List Stat:=[Sum.inr 0,Sum.inr 1,Sum.inr 2,Sum.inr 3,Sum.inr 4,Sum.inr 5,Sum.inr 6]
  set res0:=elim 7 gates (init7,[])
  set gs0:=res0.2
  have hlen0:gs0.length ≤ gates.length:=by
    have:=(elim_len_and_not 7 gates (init7,[])).1; simpa using this
  have hnot0:countNot gs0 ≤ 1:=by
    have h1:countNot gs0 ≤ countNot [] + countNot gates:=(elim_len_and_not 7 gates (init7,[])).2
    have h2:countNot gates ≤ 1:=countNot_le_one_of_unique gates huniq
    have h3:countNot [] = 0:=rfl
    omega
  have hcl0:CleanL 7 gs0:=by
    apply elim_clean 7 gates (init7,[]) hok
    · intro i
      rcases i with _ | _ | _ | _ | _ | _ | _ | i <;> simp [init7,statValid]
    · intro p g hp; simp at hp
  have hinv0:∀ x:Fin 7 -> Bool,Inv 7 (List.ofFn x) (wiresFrom gates (List.ofFn x)) res0:=by
    intro x
    apply inv_elim 7 (List.ofFn x) (by simp) gates (List.ofFn x) (init7,[]) hok
    refine ⟨by simp [init7],fun i => ?_⟩
    rcases i with _ | _ | _ | _ | _ | _ | _ | i <;>
      simp [init7,statValid,statVal,wiresFrom,List.ofFn_succ]
  have ho0_ex:∃ o0,res0.1.getD o (Sum.inl false) = Sum.inr o0 /\ o0 < 7 + gs0.length:=by
    cases hst:res0.1.getD o (Sum.inl false) with
    | inl c =>
      exfalso
      have hconst:∀ x:Fin 7 -> Bool,evalG x = c:=by
        intro x
        have h1:=((hinv0 x).2 o).2
        rw [hst] at h1
        have h2:=heval x
        rw [circuit_eval_eq] at h2
        rw [<- h2,<- h1]; rfl
      have hf:=hconst (fun _ => false)
      have ht:=hconst (fun _ => true)
      rw [evalG_eq_bool] at hf ht
      simp [evalGBool] at hf ht
      rw [hf] at ht; cases ht
    | inr o0 =>
      have hv:=((hinv0 (fun _ => false)).2 o).1
      rw [hst] at hv
      exact ⟨o0,rfl,hv⟩
  obtain ⟨o0,ho0_eq,ho0_lt⟩:=ho0_ex
  have hev0:∀ x:Fin 7 -> Bool,(wiresFrom gs0 (List.ofFn x)).getD o0 false = evalG x:=by
    intro x
    have h1:=((hinv0 x).2 o).2
    rw [ho0_eq] at h1
    have h2:=heval x
    rw [circuit_eval_eq] at h2
    exact h1.trans h2
  by_cases hcn0:countNot gs0 = 0
  ·
    refine ⟨gs0,o0,no_not_of_countNot_zero gs0 (cleanL_ok hcl0) hcn0,hlen0,?_⟩
    intro x; rw [circuit_eval_eq]; exact hev0 x
  ·
    have hcn1:countNot gs0 = 1:=by omega
    obtain ⟨p,gp,hp_eq,hp_not,hset_zero⟩:=exists_unique_not_of_countNot_one gs0 hcn1
    by_cases hreach:Reach 7 gs0 o0 (7 + p)
    ·
      suffices h13:13 ≤ gs0.length by
        exact ⟨w13Gates,19,w13_ok,by rw [w13_len]; omega,w13_eval⟩
      set res1:=elim 6 gs0 (sub2Init,[])
      set gs1:=res1.2
      have hcl1:CleanL 6 gs1:=by
        apply elim_clean 6 gs0 (sub2Init,[]) (cleanL_ok hcl0)
        · intro i
          rcases i with _ | _ | _ | _ | _ | _ | _ | i <;> simp [sub2Init,statValid]
        · intro q g hq; simp at hq
      have hinv1:∀ y:Fin 6 -> Bool,Inv 6 (List.ofFn y) (wiresFrom gs0 (List.ofFn (liftW5 y))) res1:=by
        intro y
        apply inv_elim 6 (List.ofFn y) (by simp) gs0 (List.ofFn (liftW5 y)) (sub2Init,[]) (cleanL_ok hcl0)
        refine ⟨by simp [sub2Init],fun i => ?_⟩
        rcases i with _ | _ | _ | _ | _ | _ | _ | i <;>
          simp [sub2Init,statValid,statVal,wiresFrom,List.ofFn_succ,liftW5]
      have ho1_ex:∃ o1,res1.1.getD o0 (Sum.inl false) = Sum.inr o1 /\ o1 < 6 + gs1.length:=by
        cases hst:res1.1.getD o0 (Sum.inl false) with
        | inl c =>
          exfalso
          have hconst:∀ y:Fin 6 -> Bool,evalW5 y = c:=by
            intro y
            have h1:=((hinv1 y).2 o0).2
            rw [hst] at h1
            rw [<- evalG_liftW5,<- hev0 (liftW5 y),<- h1]; rfl
          have hf:=hconst (fun _ => false)
          have ht:=hconst (fun _ => true)
          simp [evalW5] at hf ht
          rw [hf] at ht; cases ht
        | inr o1 =>
          have hv:=((hinv1 (fun _ => false)).2 o0).1
          rw [hst] at hv
          exact ⟨o1,rfl,hv⟩
      obtain ⟨o1,ho1_eq,ho1_lt⟩:=ho1_ex
      have hev1:∀ y:Fin 6 -> Bool,(wiresFrom gs1 (List.ofFn y)).getD o1 false = evalW5 y:=by
        intro y
        have h1:=((hinv1 y).2 o0).2
        rw [ho1_eq] at h1
        rw [<- evalG_liftW5,<- hev0 (liftW5 y)]
        exact h1
      have hlb_gs1:11 ≤ gs1.length - countNot gs1:=by
        by_contra hlt
        have hle10:gs1.length - countNot gs1 ≤ 10:=by omega
        obtain ⟨hsn_cl,hsn_len,_,hsn_bd,hsn_ev⟩:=stripNot_sound 6 gs1 hcl1
        set sres:=stripNot 6 gs1
        set outPair:=sres.1.getD o1 (0,false)
        apply hW5 sres.2 outPair.1 outPair.2 hsn_cl (by omega) (hsn_bd o1 ho1_lt)
        intro y
        exact (hsn_ev y o1 ho1_lt).trans (hev1 y)
      by_cases hcn_gs1:countNot gs1 = 0
      ·
        have hdp:=elim_not_dropped 6 gs0 (sub2Init,[]) p gp hp_eq hp_not hcn_gs1
        have hp_lt:p < gs0.length:=(List.getElem?_eq_some_iff.1 hp_eq).1
        obtain ⟨c,hc_simp⟩:=simplify_not_none_const _ _ (by rw [<- hp_not]; exact hdp)
        have hst_p:∀ k,p < k -> k ≤ gs0.length ->
            (elim 6 (gs0.take k) (sub2Init,[])).1.getD (7 + p) (Sum.inl false) = Sum.inl c:=by
          intro k hpk hklen
          have htake_eq:gs0.take k = gs0.take p ++ gp :: (gs0.drop (p + 1)).take (k - (p + 1)):=by
            obtain ⟨pre,post,hgs,hplen⟩:=split_at gs0 p gp hp_eq
            have h1:gs0.take p = pre:=by rw [hgs,List.take_left' hplen]
            have h2:gs0.drop (p + 1) = post:=by
              rw [hgs]; simp [List.drop_append,hplen]
            rw [h1,h2,hgs,List.take_append]
            have:k - pre.length = (k - (p + 1)) + 1:=by omega
            rw [List.take_of_length_le (by omega),this]; rfl
          rw [htake_eq,elim_len_split]
          change (elim 6 ((gs0.drop (p + 1)).take (k - (p + 1))) (elimStep 6 (elim 6 (gs0.take p) (sub2Init,[])) gp)).1.getD (7 + p) (Sum.inl false) = Sum.inl c
          have hpre_len:(elim 6 (gs0.take p) (sub2Init,[])).1.length = 7 + p:=by
            obtain ⟨t,ht,htl⟩:=elim_stat_prefix 6 (gs0.take p) (sub2Init,[])
            rw [ht,List.length_append,htl]; simp [sub2Init]; omega
          rw [elim_stat_getD_lt 6 _ _ (7 + p) (by simp [elimStep,hpre_len])]
          simp only [elimStep]
          rw [getD_snoc_len _ _ _ _ hpre_len,hp_not]
          exact hc_simp
        have hres1_p:res1.1.getD (7 + p) (Sum.inl false) = Sum.inl c:=by
          have:=hst_p gs0.length hp_lt (le_refl _)
          simpa [res1] using this
        have hne_o0:7 + p ≠ o0:=by
          intro heq
          rw [<- heq,hres1_p] at ho1_eq
          cases ho1_eq
        rcases reach_cases hreach with heq | ⟨q,gq,hq_eq,hmem_q,_⟩
        · exact absurd heq hne_o0
        · have hq_lt:q < gs0.length:=(List.getElem?_eq_some_iff.1 hq_eq).1
          have hpq:p < q:=by
            have:=cleanG_lt (hcl0 q gq hq_eq) (7 + p) hmem_q
            omega
          have hdq:=elim_const_forces_drop (7 + q) gq (hcl0 q gq hq_eq)
            (elim 6 (gs0.take q) (sub2Init,[])).1
            (6 + (elim 6 (gs0.take q) (sub2Init,[])).2.length)
            (7 + p) c hmem_q (hst_p q hpq (by omega))
          have h2drop:gs1.length + 2 ≤ gs0.length:=by
            have:=elim_drop_at_two 6 gs0 (sub2Init,[]) p q gp gq hpq hp_eq hq_eq hdp hdq
            simpa [gs1,res1] using this
          omega
      ·
        have hne2:o0 ≠ 2:=by
          intro heq
          have hx:=hev0 (fun i => decide (i.val = 2))
          rw [heq,getD_wiresFrom _ _ 2 (by simp),evalG_eq_bool] at hx
          simp [List.ofFn_succ,evalGBool] at hx
        have hreads2:∃ (q:ℕ) (gq:Gate),gs0[q]? = some gq /\ 2 ∈ gq.inputs:=by
          by_contra hno
          push Not at hno
          have hind:=eval_indep_of_unread 7 gs0 hcl0 2 hno
            (List.ofFn (fun i:Fin 7 => decide (i.val = 6)))
            (List.ofFn (fun i:Fin 7 => decide (i.val = 2 \/ i.val = 6)))
            (by simp) (by simp)
            (by intro j hj; rcases j with _ | _ | _ | _ | _ | _ | _ | j <;> simp [List.ofFn_succ] at hj ⊢)
            o0 ho0_lt hne2
          rw [hev0,hev0,evalG_eq_bool,evalG_eq_bool] at hind
          simp [evalGBool] at hind
        obtain ⟨q,gq,hq_eq,hmem2⟩:=hreads2
        have hst2:(elim 6 (gs0.take q) (sub2Init,[])).1.getD 2 (Sum.inl false) = Sum.inl false:=by
          rw [elim_stat_getD_lt 6 _ _ 2 (by simp [sub2Init])]
          rfl
        have hdq:=elim_const_forces_drop (7 + q) gq (hcl0 q gq hq_eq)
          (elim 6 (gs0.take q) (sub2Init,[])).1
          (6 + (elim 6 (gs0.take q) (sub2Init,[])).2.length)
          2 false hmem2 hst2
        have h1drop:gs1.length + 1 ≤ gs0.length:=by
          have:=elim_drop_at 6 gs0 (sub2Init,[]) q gq hq_eq hdq
          simpa [gs1,res1] using this
        omega
    ·
      refine ⟨gs0.set p ⟨GateOp.and,[0,0]⟩,o0,?_,by simp [hlen0],?_⟩
      · apply no_not_of_countNot_zero _ _ hset_zero
        intro g hg
        obtain ⟨i,hi,rfl⟩:=List.getElem_of_mem hg
        by_cases hip:i = p
        · subst hip
          rw [List.getElem_set_self (by simpa using hi)]
          exact ⟨Or.inl rfl,by decide⟩
        · rw [List.getElem_set_ne (Ne.symm hip)]
          exact cleanL_ok hcl0 _ (List.getElem_mem _)
      · intro x
        rw [circuit_eval_eq,set_dead_eval 7 gs0 o0 p ⟨GateOp.and,[0,0]⟩ hcl0 ho0_lt hreach _ (by simp)]
        exact hev0 x
end PEqualNP.Outside.L_meta_10650_aux
namespace PEqualNP.Outside.L_meta_10650_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def maskN (n:ℕ):ℕ:=(1 <<< (1 <<< n)) - 1
def pt (n:ℕ) (k:ℕ):Fin n -> Bool:=fun i => k.testBit i.val
theorem testBit_maskN (n k:ℕ):(maskN n).testBit k = decide (k < 1 <<< n):=by
  simp only [maskN,Nat.shiftLeft_eq,Nat.one_mul,Nat.testBit_two_pow_sub_one]
@[simp] theorem testBit_one_eq (n:ℕ):Nat.testBit 1 n = decide (n = 0):=by
  cases n with
  | zero => rfl
  | succ m =>
    have hlt:1 < 2 ^ (m + 1):=by
      have:2 ≤ 2 ^ (m + 1):=by
        calc 2 = 2 ^ 1:=rfl
        _ ≤ 2 ^ (m + 1):=Nat.pow_le_pow_right (by omega) (by omega)
      omega
    simp [Nat.testBit,Nat.shiftRight_eq_div_pow,Nat.div_eq_of_lt hlt]
@[simp] theorem testBit_one_shiftLeft_simp (v j:ℕ):(decide (v ≤ j) && decide (j - v = 0)) = decide (j = v):=by
  by_cases h:j = v
  · subst h; simp
  · by_cases hle:v ≤ j
    · simp [hle,show j - v ≠ 0 by omega,h]
    · simp [hle,h]
@[simp high] theorem testBit_one_shiftLeft (v j:ℕ):(1 <<< v).testBit j = decide (j = v):=by
  rw [Nat.shiftLeft_eq,Nat.one_mul,Nat.testBit_two_pow]
  exact decide_eq_decide.2 eq_comm
def encBAux (g:ℕ -> Bool):ℕ -> ℕ
  | 0 => 0
  | m + 1 => encBAux g m ||| (if g m then 1 <<< m else 0)
def encB (n:ℕ) (g:ℕ -> Bool):ℕ:=encBAux g (1 <<< n)
theorem encBAux_testBit (g:ℕ -> Bool) (m k:ℕ) :
    (encBAux g m).testBit k = (decide (k < m) && g k):=by
  induction m with
  | zero => simp [encBAux]
  | succ m ih =>
    simp only [encBAux,Nat.testBit_or,ih]
    by_cases hkm:k = m
    · subst hkm
      cases hg:g k <;> simp [testBit_one_shiftLeft]
    · by_cases hlt:k < m
      · have hlt':k < m + 1:=by omega
        cases hg:g m <;> simp [hlt,hlt',testBit_one_shiftLeft,hkm]
      · have hlt':¬ (k < m + 1):=by omega
        cases hg:g m <;> simp [hlt,hlt',testBit_one_shiftLeft,hkm]
theorem encB_testBit (n:ℕ) (g:ℕ -> Bool) (k:ℕ) :
    (encB n g).testBit k = (decide (k < 1 <<< n) && g k) :=
  encBAux_testBit g (1 <<< n) k
def inpW (n i:ℕ):ℕ:=encB n (fun k => k.testBit i)
theorem inpW_testBit (n i k:ℕ) (hk:k < 1 <<< n) :
    (inpW n i).testBit k = k.testBit i:=by
  simp [inpW,encB_testBit,hk]
theorem ofFn_pt_getD (n k i:ℕ) (hi:i < n) :
    (List.ofFn (pt n k)).getD i false = k.testBit i:=by
  simp [List.getD_eq_getElem?_getD,hi,pt]
def HasSignedOn (n rm tgt s:ℕ):Prop :=
  ∃ (sgs:List SGate) (o:ℕ) (pol:Bool),
    SCleanL n sgs /\ sgs.length ≤ s /\ o < n + sgs.length /\
    ∀ k < 1 <<< n,rm.testBit k = true ->
      xor ((sWiresFrom sgs (List.ofFn (pt n k))).getD o false) pol = tgt.testBit k
theorem hasSignedOn_mono {n rm tgt s s':ℕ} (hle:s ≤ s') (h:HasSignedOn n rm tgt s) :
    HasSignedOn n rm tgt s':=by
  obtain ⟨sgs,o,pol,hcl,hslen,ho,hev⟩:=h
  exact ⟨sgs,o,pol,hcl,Nat.le_trans hslen hle,ho,hev⟩
abbrev SStat:=Sum Bool (ℕ × Bool)
def sStatVal (w:List Bool):SStat -> Bool
  | Sum.inl c => c
  | Sum.inr (j,p) => xor (w.getD j false) p
def sStatValid (m:ℕ):SStat -> Prop
  | Sum.inl _ => True
  | Sum.inr (j,_) => j < m
theorem sStatValid_mono {m m':ℕ} (h:m ≤ m'):∀ s,sStatValid m s -> sStatValid m' s
  | Sum.inl _,_ => trivial
  | Sum.inr (_,_),hj => Nat.lt_of_lt_of_le hj h
def sGateOf (isAnd:Bool) (pa pb:Bool) (ja jb:ℕ):SGate × Bool :=
  match isAnd,pa,pb with
  | true, false,false => (⟨0,ja,jb⟩,false)
  | true, false,true  => (⟨2,ja,jb⟩,false)
  | true, true, false => (⟨3,ja,jb⟩,false)
  | true, true, true  => (⟨1,ja,jb⟩,true)
  | false,false,false => (⟨1,ja,jb⟩,false)
  | false,false,true  => (⟨3,ja,jb⟩,true)
  | false,true, false => (⟨2,ja,jb⟩,true)
  | false,true, true  => (⟨0,ja,jb⟩,true)
def sOpCombine (op:ℕ) (pa pb:Bool) (ja jb:ℕ):SGate × Bool :=
  match op with
  | 0 => sGateOf true  pa pb ja jb
  | 1 => sGateOf false pa pb ja jb
  | 2 => sGateOf true  pa (!pb) ja jb
  | _ => sGateOf true  (!pa) pb ja jb
theorem sOpCombine_eval (op:ℕ) (pa pb xa xb:Bool) (ja jb:ℕ) :
    let r:=sOpCombine op pa pb ja jb
    xor (sOpEval r.1.op xa xb) r.2 = sOpEval op (xor xa pa) (xor xb pb):=by
  rcases op with _ | _ | _ | op <;>
  · cases pa <;> cases pb <;> cases xa <;> cases xb <;> rfl
theorem sOpCombine_clean (op:ℕ) (pa pb:Bool) (ja jb m:ℕ) (hja:ja < m) (hjb:jb < m) :
    let g:=(sOpCombine op pa pb ja jb).1
    g.a < m /\ g.b < m /\ g.op < 4:=by
  rcases op with _ | _ | _ | op <;>
  · cases pa <;> cases pb <;> simp [sOpCombine,sGateOf,hja,hjb]
def sSimp (op next:ℕ) (sa sb:SStat):Option SGate × SStat :=
  match sa,sb with
  | Sum.inl c,Sum.inl d => (none,Sum.inl (sOpEval op c d))
  | Sum.inl c,Sum.inr (j,pb) =>
    match op,c with
    | 0,false => (none,Sum.inl false)
    | 0,true  => (none,Sum.inr (j,pb))
    | 1,true  => (none,Sum.inl true)
    | 1,false => (none,Sum.inr (j,pb))
    | 2,false => (none,Sum.inl false)
    | 2,true  => (none,Sum.inr (j,!pb))
    | _,true  => (none,Sum.inl false)
    | _,false => (none,Sum.inr (j,pb))
  | Sum.inr (j,pa),Sum.inl d =>
    match op,d with
    | 0,false => (none,Sum.inl false)
    | 0,true  => (none,Sum.inr (j,pa))
    | 1,true  => (none,Sum.inl true)
    | 1,false => (none,Sum.inr (j,pa))
    | 2,true  => (none,Sum.inl false)
    | 2,false => (none,Sum.inr (j,pa))
    | _,false => (none,Sum.inl false)
    | _,true  => (none,Sum.inr (j,!pa))
  | Sum.inr (ja,pa),Sum.inr (jb,pb) =>
    let r:=sOpCombine op pa pb ja jb
    (some r.1,Sum.inr (next,r.2))
theorem sSimp_sound (op:ℕ) (w:List Bool) (sa sb:SStat)
    (hva:sStatValid w.length sa) (hvb:sStatValid w.length sb) :
    let r:=sSimp op w.length sa sb
    sStatValid (w.length + r.1.toList.length) r.2 /\
    (∀ g,r.1 = some g -> g.a < w.length /\ g.b < w.length /\ g.op < 4) /\
    sStatVal (sWiresFrom r.1.toList w) r.2 = sOpEval op (sStatVal w sa) (sStatVal w sb):=by
  cases sa with
  | inl c =>
    cases sb with
    | inl d =>
      simp [sSimp,sStatValid,sStatVal]
    | inr p =>
      obtain ⟨j,pb⟩:=p
      have hj:j < w.length:=hvb
      rcases op with _ | _ | _ | op <;> cases c <;>
        simp [sSimp,sStatValid,sStatVal,sWiresFrom,sOpEval,hj]
  | inr p =>
    obtain ⟨j,pa⟩:=p
    have hj:j < w.length:=hva
    cases sb with
    | inl d =>
      rcases op with _ | _ | _ | op <;> cases d <;>
        simp [sSimp,sStatValid,sStatVal,sWiresFrom,sOpEval,hj]
    | inr q =>
      obtain ⟨k,pb⟩:=q
      have hk:k < w.length:=hvb
      dsimp only [sSimp]
      refine ⟨by simp [sStatValid],?_,?_⟩
      · intro g hg; injection hg with hg; subst hg
        exact sOpCombine_clean op pa pb j k w.length hj hk
      · simp only [Option.toList_some,sWiresFrom,List.foldl_cons,List.foldl_nil,sStatVal]
        rw [getD_snoc_eq]
        have hga:(sOpCombine op pa pb j k).1.a = j:=by
          rcases op with _ | _ | _ | op <;> cases pa <;> cases pb <;> rfl
        have hgb:(sOpCombine op pa pb j k).1.b = k:=by
          rcases op with _ | _ | _ | op <;> cases pa <;> cases pb <;> rfl
        rw [hga,hgb]
        exact sOpCombine_eval op pa pb (w.getD j false) (w.getD k false) j k
def sSubstStep (m:ℕ) (acc:List SStat × List SGate) (g:SGate):List SStat × List SGate :=
  let r:=sSimp g.op (m + acc.2.length) (acc.1.getD g.a (Sum.inl false)) (acc.1.getD g.b (Sum.inl false))
  (acc.1 ++ [r.2],acc.2 ++ r.1.toList)
def sSubst (m:ℕ) (sgs:List SGate) (acc:List SStat × List SGate):List SStat × List SGate :=
  sgs.foldl (sSubstStep m) acc
def SInv (m:ℕ) (w0 w:List Bool) (acc:List SStat × List SGate):Prop :=
  acc.1.length = w.length /\
  ∀ i,sStatValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) /\
       sStatVal (sWiresFrom acc.2 w0) (acc.1.getD i (Sum.inl false)) = w.getD i false
theorem sInv_step (m:ℕ) (w0 w:List Bool) (hw0:w0.length = m)
    (acc:List SStat × List SGate) (g:SGate) (hi:SInv m w0 w acc) :
    SInv m w0 (w ++ [sOpEval g.op (w.getD g.a false) (w.getD g.b false)]) (sSubstStep m acc g):=by
  obtain ⟨hlen,hget⟩:=hi
  set w':=sWiresFrom acc.2 w0
  have hwl:w'.length = m + acc.2.length:=by rw [length_sWiresFrom,hw0]
  have hs:=sSimp_sound g.op w' (acc.1.getD g.a (Sum.inl false)) (acc.1.getD g.b (Sum.inl false))
    (by rw [hwl]; exact (hget g.a).1) (by rw [hwl]; exact (hget g.b).1)
  simp only [hwl] at hs
  refine ⟨by simp [sSubstStep,hlen],fun i => ?_⟩
  simp only [sSubstStep]
  rw [List.length_append,<- Nat.add_assoc,sWiresFrom_append]
  by_cases hiw:i = w.length
  · subst hiw
    rw [getD_snoc_len _ _ _ _ hlen,getD_snoc_eq]
    refine ⟨hs.1,?_⟩
    rw [hs.2.2,(hget g.a).2,(hget g.b).2]
  · rw [getD_snoc_ne _ _ _ _ (by omega),getD_snoc_ne _ _ _ _ hiw]
    refine ⟨sStatValid_mono (by omega) _ (hget i).1,?_⟩
    have hv:=(hget i).1
    have he:=(hget i).2
    cases hst:acc.1.getD i (Sum.inl false) with
    | inl c => rw [hst] at he; exact he
    | inr p =>
      obtain ⟨j,pol⟩:=p
      rw [hst] at hv he
      simp only [sStatValid,sStatVal] at hv he ⊢
      rw [getD_sWiresFrom _ _ _ (by rw [hwl]; exact hv)]
      exact he
theorem sInv_subst (m:ℕ) (w0:List Bool) (hw0:w0.length = m) (sgs:List SGate) :
    ∀ w acc,SInv m w0 w acc -> SInv m w0 (sWiresFrom sgs w) (sSubst m sgs acc):=by
  induction sgs with
  | nil => intro w acc h; exact h
  | cons g sgs ih =>
    intro w acc h
    exact ih _ _ (sInv_step m w0 w hw0 acc g h)
theorem sSubst_clean (m:ℕ) (sgs:List SGate) :
    ∀ acc,(∀ i,sStatValid (m + acc.2.length) (acc.1.getD i (Sum.inl false))) ->
      SCleanL m acc.2 -> SCleanL m (sSubst m sgs acc).2:=by
  induction sgs with
  | nil => intro acc _ hc; exact hc
  | cons g sgs ih =>
    intro acc hv hc
    have hs:=sSimp_sound g.op (List.replicate (m + acc.2.length) false)
      (acc.1.getD g.a (Sum.inl false)) (acc.1.getD g.b (Sum.inl false))
      (by simpa using hv g.a) (by simpa using hv g.b)
    simp only [List.length_replicate] at hs
    apply ih
    · intro i
      simp only [sSubstStep]
      rw [List.length_append,<- Nat.add_assoc]
      by_cases hil:i = acc.1.length
      · subst hil; rw [getD_snoc_eq]; exact hs.1
      · rw [getD_snoc_ne _ _ _ _ hil]; exact sStatValid_mono (by omega) _ (hv i)
    · intro p g' hp
      simp only [sSubstStep] at hp
      by_cases hlt:p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp; exact hc p g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        set r:=sSimp g.op (m + acc.2.length) (acc.1.getD g.a (Sum.inl false)) (acc.1.getD g.b (Sum.inl false)) with hr
        cases ho:r.1 with
        | none => simp [ho] at hp
        | some g0 =>
          rw [ho] at hp
          have hp0:p - acc.2.length = 0:=by
            have:=(List.getElem?_eq_some_iff.1 hp).1; simp at this; omega
          have hpeq:p = acc.2.length:=by omega
          rw [hp0] at hp; simp at hp; subst hp; rw [hpeq]
          exact hs.2.1 g0 ho
theorem sSubst_len (m:ℕ) (sgs:List SGate) :
    ∀ acc,(sSubst m sgs acc).2.length ≤ acc.2.length + sgs.length:=by
  induction sgs with
  | nil => intro acc; simp [sSubst]
  | cons g sgs ih =>
    intro acc
    have h1:=ih (sSubstStep m acc g)
    have hstep:(sSubstStep m acc g).2.length ≤ acc.2.length + 1:=by
      simp only [sSubstStep,List.length_append]
      cases (sSimp g.op (m + acc.2.length) (acc.1.getD g.a (Sum.inl false)) (acc.1.getD g.b (Sum.inl false))).1 <;> simp
    change (sSubst m sgs (sSubstStep m acc g)).2.length ≤ acc.2.length + (sgs.length + 1)
    omega
theorem sSubst_stat_prefix (m:ℕ) (sgs:List SGate) :
    ∀ acc,∃ t,(sSubst m sgs acc).1 = acc.1 ++ t /\ t.length = sgs.length:=by
  induction sgs with
  | nil => intro acc; exact ⟨[],by simp [sSubst],rfl⟩
  | cons g sgs ih =>
    intro acc
    obtain ⟨t,ht,hl⟩:=ih (sSubstStep m acc g)
    refine ⟨(sSimp g.op (m + acc.2.length) (acc.1.getD g.a (Sum.inl false)) (acc.1.getD g.b (Sum.inl false))).2 :: t,?_,by simp [hl]⟩
    change (sSubst m sgs (sSubstStep m acc g)).1 = _
    rw [ht]; simp [sSubstStep]
theorem sSubst_stat_getD_lt (m:ℕ) (sgs:List SGate) (acc:List SStat × List SGate)
    (i:ℕ) (h:i < acc.1.length) :
    (sSubst m sgs acc).1.getD i (Sum.inl false) = acc.1.getD i (Sum.inl false):=by
  obtain ⟨t,ht,_⟩:=sSubst_stat_prefix m sgs acc
  rw [ht,List.getD_append _ _ _ _ h]
theorem sSubst_split (m:ℕ) (s1 s2:List SGate) (acc:List SStat × List SGate) :
    sSubst m (s1 ++ s2) acc = sSubst m s2 (sSubst m s1 acc):=by
  simp [sSubst,List.foldl_append]
theorem sSubst_drop_at (m:ℕ) (sgs:List SGate) (acc:List SStat × List SGate) (p:ℕ) (g:SGate)
    (hp:sgs[p]? = some g)
    (hdrop:(sSimp g.op (m + (sSubst m (sgs.take p) acc).2.length)
      ((sSubst m (sgs.take p) acc).1.getD g.a (Sum.inl false))
      ((sSubst m (sgs.take p) acc).1.getD g.b (Sum.inl false))).1 = none) :
    (sSubst m sgs acc).2.length + 1 ≤ acc.2.length + sgs.length:=by
  obtain ⟨pre,post,hsgs,hplen⟩:=split_at sgs p g hp
  have htake:sgs.take p = pre:=by rw [hsgs,List.take_left' hplen]
  rw [htake] at hdrop
  rw [hsgs,sSubst_split]
  set acc1:=sSubst m pre acc
  have h1:acc1.2.length ≤ acc.2.length + pre.length:=sSubst_len m pre acc
  have hstep:(sSubstStep m acc1 g).2 = acc1.2:=by dsimp only [sSubstStep]; rw [hdrop]; simp
  have h2:=sSubst_len m post (sSubstStep m acc1 g)
  rw [hstep] at h2
  change (sSubst m post (sSubstStep m acc1 g)).2.length + 1 ≤ acc.2.length + (pre ++ g :: post).length
  simp only [List.length_append,List.length_cons]
  omega
theorem sSimp_const_drop (op next:ℕ) (sa sb:SStat)
    (h:(∃ c,sa = Sum.inl c) \/ (∃ d,sb = Sum.inl d)) :
    (sSimp op next sa sb).1 = none:=by
  rcases h with ⟨c,rfl⟩ | ⟨d,rfl⟩
  · cases sb with
    | inl d => rfl
    | inr p => rcases op with _ | _ | _ | op <;> cases c <;> rfl
  · cases sa with
    | inl c => rfl
    | inr p => rcases op with _ | _ | _ | op <;> cases d <;> rfl
theorem sWiresFrom_getD_gate (n:ℕ) (sgs:List SGate) (p:ℕ) (g:SGate) (hp:sgs[p]? = some g)
    (ha:g.a < n + p) (hb:g.b < n + p) (w:List Bool) (hw:w.length = n) :
    (sWiresFrom sgs w).getD (n + p) false =
      sOpEval g.op ((sWiresFrom sgs w).getD g.a false) ((sWiresFrom sgs w).getD g.b false):=by
  obtain ⟨pre,post,rfl,hlen⟩:=split_at sgs p g hp
  have h1:sWiresFrom (pre ++ g :: post) w = sWiresFrom post
      (sWiresFrom pre w ++ [sOpEval g.op ((sWiresFrom pre w).getD g.a false) ((sWiresFrom pre w).getD g.b false)]):=by
    rw [sWiresFrom_append]; rfl
  have hl:(sWiresFrom pre w).length = n + p:=by rw [length_sWiresFrom,hw,hlen]
  rw [h1,getD_sWiresFrom _ _ _ (by simp [hl]),getD_snoc_len _ _ _ _ hl]
  rw [getD_sWiresFrom post _ g.a (by simp [hl]; omega),List.getD_append _ _ _ _ (by omega)]
  rw [getD_sWiresFrom post _ g.b (by simp [hl]; omega),List.getD_append _ _ _ _ (by omega)]
theorem sEval_indep_of_unread (n:ℕ) (sgs:List SGate) (hcl:SCleanL n sgs) (i:ℕ)
    (hno:∀ (p:ℕ) (g:SGate),sgs[p]? = some g -> g.a ≠ i /\ g.b ≠ i)
    (w1 w2:List Bool) (hw1:w1.length = n) (hw2:w2.length = n)
    (heq:∀ j,j ≠ i -> w1.getD j false = w2.getD j false) :
    ∀ a,a < n + sgs.length -> a ≠ i ->
      (sWiresFrom sgs w1).getD a false = (sWiresFrom sgs w2).getD a false:=by
  intro a
  induction a using Nat.strong_induction_on with
  | ind a ih =>
    intro ha hne
    by_cases hlt:a < n
    · rw [getD_sWiresFrom _ _ _ (by omega),getD_sWiresFrom _ _ _ (by omega)]
      exact heq a hne
    · have hqlt:a - n < sgs.length:=by omega
      have haeq:a = n + (a - n):=by omega
      set q:=a - n
      have hq:sgs[q]? = some sgs[q]:=List.getElem?_eq_getElem hqlt
      obtain ⟨hga,hgb,_⟩:=hcl q sgs[q] hq
      obtain ⟨hnea,hneb⟩:=hno q sgs[q] hq
      rw [haeq,sWiresFrom_getD_gate n sgs q sgs[q] hq hga hgb w1 hw1,
          sWiresFrom_getD_gate n sgs q sgs[q] hq hga hgb w2 hw2]
      rw [ih sgs[q].a (by omega) (by omega) hnea,ih sgs[q].b (by omega) (by omega) hneb]
theorem lower_or_var (n rm rm' tgt v s:ℕ) (hv:v < n)
    (hsub:∀ k < 1 <<< n,rm'.testBit k = true -> rm.testBit k = true /\ k.testBit v = false)
    (hess:∃ k1 k2,k1 < 1 <<< n /\ k2 < 1 <<< n /\ rm.testBit k1 = true /\ rm.testBit k2 = true /\
      (∀ j < n,j ≠ v -> k1.testBit j = k2.testBit j) /\ tgt.testBit k1 ≠ tgt.testBit k2)
    (hnc:∃ z1 o1,z1 < 1 <<< n /\ o1 < 1 <<< n /\ rm'.testBit z1 = true /\ rm'.testBit o1 = true /\
      tgt.testBit z1 ≠ tgt.testBit o1)
    (h:HasSignedOn n rm tgt s) :
    1 ≤ s /\ HasSignedOn n rm' tgt (s - 1):=by
  obtain ⟨sgs,o,pol,hcl,hslen,ho,hev⟩:=h
  have hnev:o ≠ v:=by
    rintro rfl
    obtain ⟨z1,o1,hz1,ho1,hrmz,hrmo,hne⟩:=hnc
    have h1:=hev z1 hz1 (hsub z1 hz1 hrmz).1
    have h2:=hev o1 ho1 (hsub o1 ho1 hrmo).1
    rw [getD_sWiresFrom _ _ o (by simp [hv]),ofFn_pt_getD n z1 o hv,(hsub z1 hz1 hrmz).2] at h1
    rw [getD_sWiresFrom _ _ o (by simp [hv]),ofFn_pt_getD n o1 o hv,(hsub o1 ho1 hrmo).2] at h2
    exact hne (h1.symm.trans h2)
  have hreads:∃ (p:ℕ) (g:SGate),sgs[p]? = some g /\ (g.a = v \/ g.b = v):=by
    by_contra hno
    push Not at hno
    obtain ⟨k1,k2,hk1,hk2,hrm1,hrm2,hagree,hne⟩:=hess
    have hind:=sEval_indep_of_unread n sgs hcl v hno
      (List.ofFn (pt n k1)) (List.ofFn (pt n k2)) (by simp) (by simp)
      (by
        intro j hj
        by_cases hjn:j < n
        · rw [ofFn_pt_getD n k1 j hjn,ofFn_pt_getD n k2 j hjn]; exact hagree j hjn hj
        · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)])
      o ho hnev
    have h1:=hev k1 hk1 hrm1
    have h2:=hev k2 hk2 hrm2
    rw [hind] at h1
    exact hne (h1.symm.trans h2)
  obtain ⟨p,g,hp,hmem⟩:=hreads
  set init:=(List.range n).map (fun j => if j = v then Sum.inl false else Sum.inr (j,false))
  set res:=sSubst n sgs (init,[])
  have hinit_len:init.length = n:=by simp [init]
  have hinit_get:∀ j,init.getD j (Sum.inl false) =
      if j < n then (if j = v then Sum.inl false else Sum.inr (j,false)) else Sum.inl false:=by
    intro j
    by_cases hjn:j < n
    · simp [init,List.getD_eq_getElem?_getD,hjn]
    · rw [List.getD_eq_default _ _ (by omega)]; simp [hjn]
  have hcl':SCleanL n res.2:=by
    apply sSubst_clean n sgs (init,[])
    · intro i; rw [hinit_get]; split_ifs <;> simp [sStatValid] <;> omega
    · intro q g' hq; simp at hq
  have hdrop:(sSimp g.op (n + (sSubst n (sgs.take p) (init,[])).2.length)
      ((sSubst n (sgs.take p) (init,[])).1.getD g.a (Sum.inl false))
      ((sSubst n (sgs.take p) (init,[])).1.getD g.b (Sum.inl false))).1 = none:=by
    apply sSimp_const_drop
    have hstv:(sSubst n (sgs.take p) (init,[])).1.getD v (Sum.inl false) = Sum.inl false:=by
      rw [sSubst_stat_getD_lt n _ _ v (by simp [hinit_len,hv]),hinit_get]; simp [hv]
    rcases hmem with rfl | rfl
    · exact Or.inl ⟨false,hstv⟩
    · exact Or.inr ⟨false,hstv⟩
  have hlen':res.2.length + 1 ≤ sgs.length:=by
    have:=sSubst_drop_at n sgs (init,[]) p g hp hdrop
    simpa [res] using this
  have hs1:1 ≤ s:=by omega
  have hinv:∀ k < 1 <<< n,rm'.testBit k = true ->
      SInv n (List.ofFn (pt n k)) (sWiresFrom sgs (List.ofFn (pt n k))) res:=by
    intro k hk hrm'
    apply sInv_subst n (List.ofFn (pt n k)) (by simp) sgs (List.ofFn (pt n k)) (init,[])
    refine ⟨by simp [hinit_len],fun j => ?_⟩
    rw [hinit_get]
    by_cases hjn:j < n
    · by_cases hjv:j = v
      · subst hjv; simp [hjn,sStatValid,sStatVal,pt,(hsub k hk hrm').2]
      · simp [hjn,hjv,sStatValid,sStatVal,sWiresFrom]
    · simp only [hjn,↓reduceIte,sStatValid,sStatVal,true_and]
      rw [List.getD_eq_default _ _ (by simp; omega)]
  cases hsto:res.1.getD o (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨z1,o1,hz1,ho1,hrmz,hrmo,hne⟩:=hnc
    have h1:=((hinv z1 hz1 hrmz).2 o).2; rw [hsto] at h1
    have h2:=((hinv o1 ho1 hrmo).2 o).2; rw [hsto] at h2
    have e1:=hev z1 hz1 (hsub z1 hz1 hrmz).1
    have e2:=hev o1 ho1 (hsub o1 ho1 hrmo).1
    simp only [sStatVal] at h1 h2
    rw [<- h1] at e1; rw [<- h2] at e2
    exact hne (e1.symm.trans e2)
  | inr pair =>
    obtain ⟨o',p'⟩:=pair
    obtain ⟨z1,_,hz1,_,hrmz,_,_⟩:=hnc
    have ho':o' < n + res.2.length:=by
      have:=((hinv z1 hz1 hrmz).2 o).1; rwa [hsto] at this
    refine ⟨hs1,res.2,o',xor p' pol,hcl',by omega,ho',fun k hk hrm' => ?_⟩
    have h1:=((hinv k hk hrm').2 o).2
    rw [hsto] at h1
    simp only [sStatVal] at h1
    have e1:=hev k hk (hsub k hk hrm').1
    rw [<- e1,<- h1]
    cases ((sWiresFrom res.2 (List.ofFn (pt n k))).getD o' false) <;> cases p' <;> cases pol <;> rfl
def embedPt (vMap:List ℕ) (oM k:ℕ):ℕ :=
  (List.range vMap.length).foldl
    (fun acc i => if k.testBit i then acc ||| (1 <<< vMap.getD i 0) else acc) oM
theorem embedPt_testBit_aux (vMap:List ℕ) (oM k j:ℕ) :
    ∀ L:List ℕ,∀ acc:ℕ,
      (L.foldl (fun a i => if k.testBit i then a ||| (1 <<< vMap.getD i 0) else a) acc).testBit j =
      (acc.testBit j || L.any (fun i => k.testBit i && decide (vMap.getD i 0 = j))):=by
  intro L
  induction L with
  | nil => intro acc; simp
  | cons i L ih =>
    intro acc
    simp only [List.foldl_cons,List.any_cons,ih]
    cases hk:k.testBit i with
    | false => simp
    | true =>
      simp only [↓reduceIte,Nat.testBit_or,Bool.true_and,Bool.or_assoc]
      rw [testBit_one_shiftLeft]
      have:decide (j = vMap.getD i 0) = decide (vMap.getD i 0 = j):=decide_eq_decide.2 eq_comm
      rw [this]
theorem embedPt_testBit (vMap:List ℕ) (oM k j:ℕ) :
    (embedPt vMap oM k).testBit j =
      (oM.testBit j || (List.range vMap.length).any (fun i => k.testBit i && decide (vMap.getD i 0 = j))) :=
  embedPt_testBit_aux vMap oM k j (List.range vMap.length) oM
def findIdxList (vMap:List ℕ) (j:ℕ):Option ℕ :=
  (List.range vMap.length).find? (fun i => vMap.getD i 0 == j)
theorem iso_bound (n m rm tgt baseTgt oM s:ℕ) (vMap:List ℕ)
    (hvm_len:vMap.length = m)
    (hvm_nodup:vMap.Nodup)
    (hvm_disj:∀ i < m,oM.testBit (vMap.getD i 0) = false)
    (hemb:∀ k < 1 <<< m,
      embedPt vMap oM k < 1 <<< n /\
      rm.testBit (embedPt vMap oM k) = true /\
      tgt.testBit (embedPt vMap oM k) = baseTgt.testBit k)
    (hnc:∃ z1 o1,z1 < 1 <<< m /\ o1 < 1 <<< m /\ baseTgt.testBit z1 ≠ baseTgt.testBit o1)
    (h:HasSignedOn n rm tgt s) :
    HasSignedOn m (maskN m) baseTgt s:=by
  obtain ⟨sgs,o,pol,hcl,hslen,ho,hev⟩:=h
  set init:List SStat:=(List.range n).map fun j =>
    match findIdxList vMap j with
    | some i => Sum.inr (i,false)
    | none   => Sum.inl (oM.testBit j)
  set res:=sSubst m sgs (init,[])
  have hinit_len:init.length = n:=by simp [init]
  have hinit_get:∀ j,init.getD j (Sum.inl false) =
      if j < n then
        match findIdxList vMap j with
        | some i => Sum.inr (i,false)
        | none   => Sum.inl (oM.testBit j)
      else Sum.inl false:=by
    intro j
    by_cases hjn:j < n
    · simp [init,List.getD_eq_getElem?_getD,hjn]
    · rw [List.getD_eq_default _ _ (by omega)]; simp [hjn]
  have hfind_lt:∀ j i,findIdxList vMap j = some i -> i < m /\ vMap.getD i 0 = j:=by
    intro j i hf
    have hmem:=List.mem_of_find?_eq_some hf
    have hpred:=List.find?_some hf
    simp only [List.mem_range,beq_iff_eq] at hmem hpred
    exact ⟨by omega,hpred⟩
  have hcl':SCleanL m res.2:=by
    apply sSubst_clean m sgs (init,[])
    · intro j; rw [hinit_get]
      split_ifs
      · cases hf:findIdxList vMap j with
        | none => trivial
        | some i => exact (hfind_lt j i hf).1
      · trivial
    · intro q g hq; simp at hq
  have hlen':res.2.length ≤ s:=by
    have h1:res.2.length ≤ 0 + sgs.length:=sSubst_len m sgs (init,[])
    omega
  have hinv:∀ k < 1 <<< m,
      SInv m (List.ofFn (pt m k)) (sWiresFrom sgs (List.ofFn (pt n (embedPt vMap oM k)))) res:=by
    intro k hk
    apply sInv_subst m (List.ofFn (pt m k)) (by simp) sgs _ (init,[])
    refine ⟨by simp [hinit_len],fun j => ?_⟩
    rw [hinit_get]
    by_cases hjn:j < n
    · simp only [hjn,↓reduceIte]
      cases hf:findIdxList vMap j with
      | some i =>
        obtain ⟨him,hvi⟩:=hfind_lt j i hf
        refine ⟨by simp [sStatValid,him],?_⟩
        simp only [sStatVal,sWiresFrom,List.foldl_nil,Bool.xor_false,ofFn_pt_getD m k i him,
          ofFn_pt_getD n _ j hjn,embedPt_testBit]
        have hoj:oM.testBit j = false:=by rw [<- hvi]; exact hvm_disj i him
        rw [hoj,Bool.false_or]
        symm
        cases hki:k.testBit i with
        | true =>
          rw [List.any_eq_true]
          refine ⟨i,List.mem_range.2 (by omega),?_⟩
          simp only [Bool.and_eq_true,decide_eq_true_eq]
          exact ⟨hki,hvi⟩
        | false =>
          rw [List.any_eq_false]
          intro i' hi'
          rw [List.mem_range] at hi'
          by_cases heqi:i' = i
          · subst heqi; simp [hki]
          · have hne:vMap.getD i' 0 ≠ j:=by
              rw [<- hvi]
              have h1:vMap.getD i' 0 = vMap[i']:=by simp [List.getD_eq_getElem?_getD,hi']
              have h2:vMap.getD i 0 = vMap[i]:=by simp [List.getD_eq_getElem?_getD,hvm_len,him]
              rw [h1,h2]
              intro heq
              exact heqi ((List.Nodup.getElem_inj_iff hvm_nodup).1 heq)
            simp only [Bool.and_eq_true,decide_eq_true_eq,not_and]
            intro _; exact hne
      | none =>
        refine ⟨trivial,?_⟩
        simp only [sStatVal,ofFn_pt_getD n _ j hjn,embedPt_testBit]
        have hnone:(List.range vMap.length).any (fun i => k.testBit i && decide (vMap.getD i 0 = j)) = false:=by
          rw [List.any_eq_false]
          intro i hi
          have hfp:=List.find?_eq_none.1 hf i hi
          simp only [beq_iff_eq] at hfp
          simp only [Bool.and_eq_true,decide_eq_true_eq,not_and]
          intro _; exact hfp
        rw [hnone,Bool.or_false]
    · simp only [hjn,↓reduceIte,sStatValid,sStatVal,true_and]
      rw [List.getD_eq_default _ _ (by simp; omega)]
  cases hsto:res.1.getD o (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨z1,o1,hz1,ho1,hne⟩:=hnc
    have h1:=((hinv z1 hz1).2 o).2; rw [hsto] at h1
    have h2:=((hinv o1 ho1).2 o).2; rw [hsto] at h2
    have e1:=hev (embedPt vMap oM z1) (hemb z1 hz1).1 (hemb z1 hz1).2.1
    have e2:=hev (embedPt vMap oM o1) (hemb o1 ho1).1 (hemb o1 ho1).2.1
    simp only [sStatVal] at h1 h2
    rw [<- h1,(hemb z1 hz1).2.2] at e1
    rw [<- h2,(hemb o1 ho1).2.2] at e2
    exact hne (e1.symm.trans e2)
  | inr pair =>
    obtain ⟨o',p'⟩:=pair
    obtain ⟨z1,_,hz1,_,_⟩:=hnc
    have ho':o' < m + res.2.length:=by
      have:=((hinv z1 hz1).2 o).1; rwa [hsto] at this
    refine ⟨res.2,o',xor p' pol,hcl',hlen',ho',fun k hk _ => ?_⟩
    have h1:=((hinv k hk).2 o).2
    rw [hsto] at h1
    simp only [sStatVal] at h1
    have e1:=hev (embedPt vMap oM k) (hemb k hk).1 (hemb k hk).2.1
    rw [(hemb k hk).2.2,<- h1] at e1
    rw [<- e1]
    cases ((sWiresFrom res.2 (List.ofFn (pt m k))).getD o' false) <;> cases p' <;> cases pol <;> rfl
def sLiveStep (n p:ℕ) (g:SGate) (L:List ℕ):List ℕ :=
  if (n + p) ∈ L then
    let L1:=L.filter (· != n + p)
    let L2:=if g.a ∈ L1 then L1 else g.a :: L1
    if g.b ∈ L2 then L2 else g.b :: L2
  else L
theorem length_filter_ne_lt {α:Type} [BEq α] [LawfulBEq α] (L:List α) (x:α) (hx:x ∈ L) :
    (L.filter (· != x)).length + 1 ≤ L.length:=by
  induction L with
  | nil => cases hx
  | cons a L ih =>
    simp only [List.filter_cons,List.length_cons]
    rcases List.mem_cons.1 hx with rfl | hx'
    · simp
      exact List.length_filter_le _ _
    · have hih:=ih hx'
      cases h:(a != x) <;> simp <;> omega
theorem sLiveStep_length (n p:ℕ) (g:SGate) (L:List ℕ) :
    (sLiveStep n p g L).length ≤ L.length + 1:=by
  unfold sLiveStep
  by_cases h1:n + p ∈ L
  · simp only [h1,↓reduceIte]
    have hflt:=length_filter_ne_lt L (n + p) h1
    set L1:=L.filter (· != n + p)
    set L2:=if g.a ∈ L1 then L1 else g.a :: L1
    have hL2:L2.length ≤ L1.length + 1:=by
      dsimp only [L2]; split_ifs <;> simp
    have hL3:(if g.b ∈ L2 then L2 else g.b :: L2).length ≤ L2.length + 1:=by
      split_ifs <;> simp
    omega
  · simp only [h1,↓reduceIte]; omega
def sLiveAt (n:ℕ) (sgs:List SGate):ℕ -> List ℕ -> List ℕ
  | 0,L => L
  | p + 1,L =>
    match sgs[p]? with
    | some g => sLiveAt n sgs p (sLiveStep n p g L)
    | none   => sLiveAt n sgs p L
theorem sLiveAt_length (n:ℕ) (sgs:List SGate) :
    ∀ p L,(sLiveAt n sgs p L).length ≤ L.length + p:=by
  intro p
  induction p with
  | zero => intro L; simp [sLiveAt]
  | succ p ih =>
    intro L
    simp only [sLiveAt]
    cases hg:sgs[p]? with
    | none => simp only; have:=ih L; omega
    | some g =>
      simp only
      have h1:=ih (sLiveStep n p g L)
      have h2:=sLiveStep_length n p g L
      omega
theorem sLiveStep_lt (n p:ℕ) (g:SGate) (L:List ℕ) (hL:∀ u ∈ L,u < n + (p + 1))
    (hga:g.a < n + p) (hgb:g.b < n + p) :
    ∀ v ∈ sLiveStep n p g L,v < n + p:=by
  intro v hv
  unfold sLiveStep at hv
  by_cases hmem:n + p ∈ L
  · simp only [hmem,↓reduceIte] at hv
    set L1:=L.filter (· != n + p)
    set L2:=if g.a ∈ L1 then L1 else g.a :: L1
    have h1:∀ x ∈ L1,x < n + p:=by
      intro x hx
      obtain ⟨hxL,hxne⟩:=List.mem_filter.1 hx
      have hlt:=hL x hxL
      simp only [bne_iff_ne,ne_eq] at hxne
      omega
    have h2:∀ x ∈ L2,x < n + p:=by
      intro x hx
      dsimp only [L2] at hx
      split_ifs at hx
      · exact h1 x hx
      · rcases List.mem_cons.1 hx with rfl | hx'
        · exact hga
        · exact h1 x hx'
    by_cases hb:g.b ∈ L2
    · rw [if_pos hb] at hv; exact h2 v hv
    · rw [if_neg hb] at hv
      rcases List.mem_cons.1 hv with rfl | hv'
      · exact hgb
      · exact h2 v hv'
  · simp only [hmem,↓reduceIte] at hv
    have hlt:=hL v hv
    have hne:v ≠ n + p:=fun h => hmem (h ▸ hv)
    omega
theorem sLiveAt_eval_eq (n:ℕ) (sgs:List SGate) (hcl:SCleanL n sgs)
    (w1 w2:List Bool) (hw1:w1.length = n) (hw2:w2.length = n) :
    ∀ p ≤ sgs.length,∀ L:List ℕ,
      (∀ u ∈ L,u < n + p) ->
      (∀ u ∈ sLiveAt n sgs p L,(sWiresFrom sgs w1).getD u false = (sWiresFrom sgs w2).getD u false) ->
      ∀ u ∈ L,(sWiresFrom sgs w1).getD u false = (sWiresFrom sgs w2).getD u false:=by
  intro p
  induction p with
  | zero => intro _ L _ h; exact h
  | succ p ih =>
    intro hp L hLlt hrec
    have hget:sgs[p]? = some sgs[p]:=List.getElem?_eq_getElem (by omega)
    simp only [sLiveAt,hget] at hrec
    obtain ⟨hga,hgb,_⟩:=hcl p sgs[p] hget
    set L':=sLiveStep n p sgs[p] L
    have hL'lt:∀ v ∈ L',v < n + p:=sLiveStep_lt n p sgs[p] L hLlt hga hgb
    have hL'eq:=ih (by omega) L' hL'lt hrec
    intro u hu
    by_cases hup:u = n + p
    · subst hup
      have hmem:n + p ∈ L:=hu
      have hga_mem:sgs[p].a ∈ L':=by
        unfold L' sLiveStep
        simp only [hmem,↓reduceIte]
        set L1:=L.filter (· != n + p)
        set L2:=if sgs[p].a ∈ L1 then L1 else sgs[p].a :: L1
        have hmem2:sgs[p].a ∈ L2:=by dsimp only [L2]; split_ifs with h <;> simp [h]
        by_cases hb:sgs[p].b ∈ L2
        · rw [if_pos hb]; exact hmem2
        · rw [if_neg hb]; exact List.mem_cons_of_mem _ hmem2
      have hgb_mem:sgs[p].b ∈ L':=by
        unfold L' sLiveStep
        simp only [hmem,↓reduceIte]
        set L1:=L.filter (· != n + p)
        set L2:=if sgs[p].a ∈ L1 then L1 else sgs[p].a :: L1
        by_cases hb:sgs[p].b ∈ L2
        · rw [if_pos hb]; exact hb
        · rw [if_neg hb]; exact List.mem_cons_self
      rw [sWiresFrom_getD_gate n sgs p sgs[p] hget hga hgb w1 hw1,
          sWiresFrom_getD_gate n sgs p sgs[p] hget hga hgb w2 hw2,
          hL'eq sgs[p].a hga_mem,hL'eq sgs[p].b hgb_mem]
    · have hu_mem:u ∈ L':=by
        unfold L' sLiveStep
        by_cases hmem:n + p ∈ L
        · simp only [hmem,↓reduceIte]
          set L1:=L.filter (· != n + p)
          set L2:=if sgs[p].a ∈ L1 then L1 else sgs[p].a :: L1
          have hu1:u ∈ L1:=List.mem_filter.2 ⟨hu,by simp [hup]⟩
          have hu2:u ∈ L2:=by dsimp only [L2]; split_ifs <;> simp [hu1]
          by_cases hb:sgs[p].b ∈ L2
          · rw [if_pos hb]; exact hu2
          · rw [if_neg hb]; exact List.mem_cons_of_mem _ hu2
        · simp only [hmem,↓reduceIte]; exact hu
      exact hL'eq u hu_mem
theorem sLiveAt_lt_n (n:ℕ) (sgs:List SGate) (hcl:SCleanL n sgs) :
    ∀ p ≤ sgs.length,∀ L:List ℕ,(∀ u ∈ L,u < n + p) -> ∀ u ∈ sLiveAt n sgs p L,u < n:=by
  intro p
  induction p with
  | zero => intro _ L hL u hu; simpa [sLiveAt] using hL u hu
  | succ p ih =>
    intro hp L hL
    have hget:sgs[p]? = some sgs[p]:=List.getElem?_eq_getElem (by omega)
    simp only [sLiveAt,hget]
    obtain ⟨hga,hgb,_⟩:=hcl p sgs[p] hget
    exact ih (by omega) _ (sLiveStep_lt n p sgs[p] L hL hga hgb)
theorem nodup_subset_length {α:Type} [DecidableEq α] (A B:List α)
    (hnd:A.Nodup) (hsub:∀ x ∈ A,x ∈ B):A.length ≤ B.length:=by
  induction A generalizing B with
  | nil => simp
  | cons a A ih =>
    obtain ⟨hna,hnd'⟩:=List.nodup_cons.1 hnd
    have haB:a ∈ B:=hsub a List.mem_cons_self
    have hsub':∀ x ∈ A,x ∈ B.erase a:=by
      intro x hx
      have hne:x ≠ a:=fun h => hna (h ▸ hx)
      exact List.mem_erase_of_ne hne |>.2 (hsub x (List.mem_cons_of_mem _ hx))
    have h1:=ih (B.erase a) hnd' hsub'
    have h2:=List.length_erase_of_mem haB
    have h3:1 ≤ B.length:=List.length_pos_of_mem haB
    simp only [List.length_cons]
    omega
theorem lower_essential (n rm tgt s:ℕ) (ess:List ℕ)
    (hnd:ess.Nodup)
    (hess:∀ v ∈ ess,v < n /\
      ∃ k1 k2,k1 < 1 <<< n /\ k2 < 1 <<< n /\ rm.testBit k1 = true /\ rm.testBit k2 = true /\
        (∀ j < n,j ≠ v -> k1.testBit j = k2.testBit j) /\ tgt.testBit k1 ≠ tgt.testBit k2)
    (h:HasSignedOn n rm tgt s) :
    ess.length ≤ s + 1:=by
  obtain ⟨sgs,o,pol,hcl,hslen,ho,hev⟩:=h
  set L0:=sLiveAt n sgs sgs.length [o]
  have hL0_len:L0.length ≤ sgs.length + 1:=by
    have:=sLiveAt_length n sgs sgs.length [o]; simp [L0] at this ⊢; omega
  have hL0_lt:∀ u ∈ L0,u < n :=
    sLiveAt_lt_n n sgs hcl sgs.length (le_refl _) [o] (by intro u hu; simp at hu; subst hu; exact ho)
  have hsub:∀ v ∈ ess,v ∈ L0:=by
    intro v hv
    by_contra hnot
    obtain ⟨hvn,k1,k2,hk1,hk2,hrm1,hrm2,hagree,hne⟩:=hess v hv
    have heq_o:=sLiveAt_eval_eq n sgs hcl (List.ofFn (pt n k1)) (List.ofFn (pt n k2))
      (by simp) (by simp) sgs.length (le_refl _) [o]
      (by intro u hu; simp at hu; subst hu; exact ho)
      (by
        intro u hu
        have hun:=hL0_lt u hu
        have huv:u ≠ v:=fun h => hnot (h ▸ hu)
        rw [getD_sWiresFrom _ _ u (by simp [hun]),getD_sWiresFrom _ _ u (by simp [hun]),
            ofFn_pt_getD n k1 u hun,ofFn_pt_getD n k2 u hun]
        exact hagree u hun huv)
      o List.mem_cons_self
    have e1:=hev k1 hk1 hrm1
    have e2:=hev k2 hk2 hrm2
    rw [heq_o] at e1
    exact hne (e1.symm.trans e2)
  have:=nodup_subset_length ess L0 hnd hsub
  omega
structure SliceData where
  zM:ℕ
  oM:ℕ
  orM:ℕ
  L:ℕ
  baseId:ℕ
  vMap:List ℕ
  rm:ℕ
  low:ℕ
  base:List ℕ
deriving Repr
def projSl (sl:SliceData) (w:ℕ):ℕ :=
  let p:=w &&& sl.rm
  if p == sl.rm then 0
  else if p != 0 && (p &&& sl.low) != 0 then p ^^^ sl.rm
  else p
def isEssOn (n rm tgt v:ℕ):Bool :=
  (List.range (1 <<< n)).any fun k =>
    rm.testBit k && rm.testBit (k ^^^ (1 <<< v)) && (tgt.testBit k != tgt.testBit (k ^^^ (1 <<< v)))
def hasZeroAndOne (n rm tgt:ℕ):Bool :=
  (List.range (1 <<< n)).any (fun k => rm.testBit k && !tgt.testBit k) &&
  (List.range (1 <<< n)).any (fun k => rm.testBit k && tgt.testBit k)
def maskSub (n zM oM:ℕ):ℕ :=
  encB n (fun k => (k &&& zM == 0) && (k &&& oM == oM))
def checkEmbed (n m rm tgt baseTgt oM:ℕ) (vMap:List ℕ):Bool :=
  (vMap.length == m) &&
  vMap.Nodup &&
  (List.range m).all (fun i => !oM.testBit (vMap.getD i 0)) &&
  (List.range (1 <<< m)).all (fun k =>
    let e:=embedPt vMap oM k
    (e < 1 <<< n) && rm.testBit e && (tgt.testBit e == baseTgt.testBit k))
def sliceOK (n tgt:ℕ) (bases:Array (ℕ × ℕ × ℕ)) (sl:SliceData):Bool :=
  let orVars:=(List.range n).filter (fun v => sl.orM.testBit v)
  let rm0:=maskSub n (sl.zM ||| sl.orM) sl.oM
  (sl.rm == maskSub n sl.zM sl.oM) &&
  ((sl.rm &&& sl.low) != 0) &&
  (sl.zM &&& sl.orM == 0) &&
  (sl.oM &&& sl.orM == 0) &&
  (sl.orM < 1 <<< n) &&
  (sl.base.all fun b => (List.range n).any fun i => projSl sl (inpW n i) == b) &&
  hasZeroAndOne n sl.rm tgt &&
  if sl.vMap.isEmpty then
    (sl.L + 1 ≤ orVars.length) && orVars.all (fun v => isEssOn n sl.rm tgt v)
  else
    hasZeroAndOne n rm0 tgt &&
    (orVars.all fun v =>
      (List.range (1 <<< n)).all fun k =>
        if sl.rm.testBit k && k.testBit v then tgt.testBit k else true) &&
    (if h:sl.baseId < bases.size then
      let (bm,bTgt,bL):=bases[sl.baseId]
      (sl.L ≤ orVars.length + bL) &&
      checkEmbed n bm rm0 tgt bTgt sl.oM sl.vMap &&
      hasZeroAndOne bm (maskN bm) bTgt
    else
      (sl.L ≤ orVars.length + (sl.vMap.length - 1)) &&
      sl.vMap.Nodup &&
      sl.vMap.all (fun v => (v < n) && isEssOn n rm0 tgt v))
theorem isEssOn_sound (n rm tgt v:ℕ) (hv:v < n) (h:isEssOn n rm tgt v = true) :
    ∃ k1 k2,k1 < 1 <<< n /\ k2 < 1 <<< n /\ rm.testBit k1 = true /\ rm.testBit k2 = true /\
      (∀ j < n,j ≠ v -> k1.testBit j = k2.testBit j) /\ tgt.testBit k1 ≠ tgt.testBit k2:=by
  simp only [isEssOn,List.any_eq_true,List.mem_range,Bool.and_eq_true,bne_iff_ne] at h
  obtain ⟨k,hk,⟨hrm1,hrm2⟩,hne⟩:=h
  have hlt2:k ^^^ (1 <<< v) < 1 <<< n:=by
    have hvlt:1 <<< v < 1 <<< n:=by
      simp only [Nat.shiftLeft_eq,Nat.one_mul]
      exact Nat.pow_lt_pow_right (by omega) hv
    simpa [Nat.shiftLeft_eq] using
      Nat.xor_lt_two_pow (by simpa [Nat.shiftLeft_eq] using hk) (by simpa [Nat.shiftLeft_eq] using hvlt)
  refine ⟨k,k ^^^ (1 <<< v),hk,hlt2,hrm1,hrm2,?_,hne⟩
  intro j hjn hjv
  simp [Nat.testBit_xor,testBit_one_shiftLeft,hjv]
theorem hasZeroAndOne_sound (n rm tgt:ℕ) (h:hasZeroAndOne n rm tgt = true) :
    ∃ z1 o1,z1 < 1 <<< n /\ o1 < 1 <<< n /\ rm.testBit z1 = true /\ rm.testBit o1 = true /\
      tgt.testBit z1 ≠ tgt.testBit o1:=by
  simp only [hasZeroAndOne,Bool.and_eq_true,List.any_eq_true,List.mem_range,Bool.not_eq_true'] at h
  obtain ⟨⟨z1,hz1,hrmz,htz⟩,⟨o1,ho1,hrmo,hto⟩⟩:=h
  exact ⟨z1,o1,hz1,ho1,hrmz,hrmo,by rw [htz,hto]; decide⟩
theorem peel_or_vars (n zM oM tgt:ℕ) (vs:List ℕ) :
    ∀ (zCur s:ℕ),
      (∀ v ∈ vs,v < n /\ zCur.testBit v = false /\ oM.testBit v = false /\
        ∀ k < 1 <<< n,(maskSub n zCur oM).testBit k = true -> k.testBit v = true -> tgt.testBit k = true) ->
      vs.Nodup ->
      (∃ z1 o1,z1 < 1 <<< n /\ o1 < 1 <<< n /\
        (maskSub n (zCur ||| vs.foldl (fun a v => a ||| (1 <<< v)) 0) oM).testBit z1 = true /\
        (maskSub n (zCur ||| vs.foldl (fun a v => a ||| (1 <<< v)) 0) oM).testBit o1 = true /\
        tgt.testBit z1 = false /\ tgt.testBit o1 = true) ->
      HasSignedOn n (maskSub n zCur oM) tgt s ->
      vs.length ≤ s /\
      HasSignedOn n (maskSub n (zCur ||| vs.foldl (fun a v => a ||| (1 <<< v)) 0) oM) tgt (s - vs.length):=by
  induction vs with
  | nil =>
    intro zCur s _ _ _ hs
    simp only [List.foldl_nil,Nat.or_zero,List.length_nil,Nat.zero_le,Nat.sub_zero,true_and]
    exact hs
  | cons v vs ih =>
    intro zCur s hvs hnd hzo hs
    obtain ⟨hv_not,hnd'⟩:=List.nodup_cons.1 hnd
    obtain ⟨hvn,hzv,hov,hforce⟩:=hvs v List.mem_cons_self
    set zNext:=zCur ||| (1 <<< v)
    have hfold_shift:∀ (L:List ℕ) (acc:ℕ),
        L.foldl (fun a w => a ||| (1 <<< w)) acc = acc ||| L.foldl (fun a w => a ||| (1 <<< w)) 0:=by
      intro L
      induction L with
      | nil => intro acc; simp
      | cons w L ihl =>
        intro acc
        simp only [List.foldl_cons,Nat.zero_or]
        rw [ihl (acc ||| (1 <<< w)),ihl (1 <<< w),Nat.or_assoc]
    have hmask_eq:zCur ||| (v :: vs).foldl (fun a w => a ||| (1 <<< w)) 0 =
        zNext ||| vs.foldl (fun a w => a ||| (1 <<< w)) 0:=by
      simp only [List.foldl_cons,Nat.zero_or]
      rw [hfold_shift vs (1 <<< v),<- Nat.or_assoc]
    rw [hmask_eq] at hzo ⊢
    obtain ⟨z1,o1,hz1,ho1,hrmz,hrmo,htz,hto⟩:=hzo
    have hsub_mask:∀ z1' z2' k,k < 1 <<< n -> (z1' &&& z2' = z1') ->
        (maskSub n z2' oM).testBit k = true -> (maskSub n z1' oM).testBit k = true:=by
      intro z1' z2' k hk hle h2
      simp only [maskSub,encB_testBit,hk,decide_true,Bool.true_and,Bool.and_eq_true,beq_iff_eq] at h2 ⊢
      refine ⟨?_,h2.2⟩
      apply Nat.eq_of_testBit_eq
      intro i
      have hi2:=congrArg (fun x => x.testBit i) h2.1
      have hle_i:=congrArg (fun x => x.testBit i) hle
      simp only [Nat.testBit_and,Nat.zero_testBit] at hi2 hle_i ⊢
      rw [<- hle_i]
      cases hk':k.testBit i <;> cases hz2':z2'.testBit i <;> cases hz1':z1'.testBit i <;>
        simp [hk',hz2',hz1'] at hi2 hle_i ⊢
    have hsub_cur:∀ k < 1 <<< n,(maskSub n zNext oM).testBit k = true ->
        (maskSub n zCur oM).testBit k = true /\ k.testBit v = false:=by
      intro k hk h2
      refine ⟨hsub_mask zCur zNext k hk (by apply Nat.eq_of_testBit_eq; intro i; simp [zNext,Nat.testBit_and,Nat.testBit_or]; cases zCur.testBit i <;> simp) h2,?_⟩
      simp only [maskSub,encB_testBit,hk,decide_true,Bool.true_and,Bool.and_eq_true,beq_iff_eq] at h2
      have hv0:=congrArg (fun x => x.testBit v) h2.1
      simp [zNext,Nat.testBit_and,Nat.testBit_or,testBit_one_shiftLeft] at hv0
      exact hv0
    have hrmz_next:(maskSub n zNext oM).testBit z1 = true :=
      hsub_mask zNext _ z1 hz1 (by apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and,Nat.testBit_or]; cases zNext.testBit i <;> simp) hrmz
    have hrmo_next:(maskSub n zNext oM).testBit o1 = true :=
      hsub_mask zNext _ o1 ho1 (by apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and,Nat.testBit_or]; cases zNext.testBit i <;> simp) hrmo
    have hz1_flip_lt:z1 ||| (1 <<< v) < 1 <<< n:=by
      have hvlt:1 <<< v < 1 <<< n:=by
        simp only [Nat.shiftLeft_eq,Nat.one_mul]; exact Nat.pow_lt_pow_right (by omega) hvn
      simpa [Nat.shiftLeft_eq] using
        Nat.or_lt_two_pow (by simpa [Nat.shiftLeft_eq] using hz1) (by simpa [Nat.shiftLeft_eq] using hvlt)
    have hrm_z1_cur:(maskSub n zCur oM).testBit z1 = true:=(hsub_cur z1 hz1 hrmz_next).1
    have hrm_z1f_cur:(maskSub n zCur oM).testBit (z1 ||| (1 <<< v)) = true:=by
      simp only [maskSub,encB_testBit,hz1,hz1_flip_lt,decide_true,Bool.true_and,Bool.and_eq_true,beq_iff_eq] at hrm_z1_cur ⊢
      constructor
      · apply Nat.eq_of_testBit_eq; intro i
        have hi:=congrArg (fun x => x.testBit i) hrm_z1_cur.1
        simp only [Nat.testBit_and,Nat.testBit_or,testBit_one_shiftLeft,Nat.zero_testBit] at hi ⊢
        by_cases hiv:i = v
        · subst hiv; simp [hzv]
        · simp [hiv,hi]
      · apply Nat.eq_of_testBit_eq; intro i
        have hi:=congrArg (fun x => x.testBit i) hrm_z1_cur.2
        simp only [Nat.testBit_and,Nat.testBit_or,testBit_one_shiftLeft] at hi ⊢
        by_cases hiv:i = v
        · subst hiv; simp [hov]
        · simp [hiv,hi]
    have htz1f:tgt.testBit (z1 ||| (1 <<< v)) = true :=
      hforce (z1 ||| (1 <<< v)) hz1_flip_lt hrm_z1f_cur (by simp [Nat.testBit_or,testBit_one_shiftLeft])
    have hstep:=lower_or_var n (maskSub n zCur oM) (maskSub n zNext oM) tgt v s hvn hsub_cur
      ⟨z1,z1 ||| (1 <<< v),hz1,hz1_flip_lt,hrm_z1_cur,hrm_z1f_cur,
       fun j _ hjv => by simp [Nat.testBit_or,testBit_one_shiftLeft,hjv],
       by rw [htz,htz1f]; decide⟩
      ⟨z1,o1,hz1,ho1,hrmz_next,hrmo_next,by rw [htz,hto]; decide⟩
      hs
    have hrec:=ih zNext (s - 1)
      (by
        intro w hw
        obtain ⟨hwn,hzw,how,hfw⟩:=hvs w (List.mem_cons_of_mem _ hw)
        have hne:w ≠ v:=fun h => hv_not (h ▸ hw)
        refine ⟨hwn,?_,how,fun k hk hrmk hkw => hfw k hk (hsub_cur k hk hrmk).1 hkw⟩
        simp [zNext,Nat.testBit_or,testBit_one_shiftLeft,hzw,hne])
      hnd' ⟨z1,o1,hz1,ho1,hrmz,hrmo,htz,hto⟩ hstep.2
    simp only [List.length_cons]
    refine ⟨by omega,?_⟩
    have hsub_eq:s - 1 - vs.length = s - (vs.length + 1):=by omega
    rw [<- hsub_eq]; exact hrec.2
theorem sliceOK_sound (n tgt:ℕ) (bases:Array (ℕ × ℕ × ℕ))
    (hbases:∀ i (hi:i < bases.size),
      let (bm,bTgt,bL):=bases[i]
      ∀ s,HasSignedOn bm (maskN bm) bTgt s -> bL ≤ s)
    (sl:SliceData) (hok:sliceOK n tgt bases sl = true) :
    ∀ s,HasSignedOn n sl.rm tgt s -> sl.L ≤ s:=by
  intro s hs
  unfold sliceOK at hok
  dsimp only at hok
  set orVars:=(List.range n).filter (fun v => sl.orM.testBit v)
  set rm0:=maskSub n (sl.zM ||| sl.orM) sl.oM
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hrm_eq,_⟩,hdisj_z⟩,hdisj_o⟩,hor_lt⟩,_⟩,_⟩,hbranch⟩:=hok
  rw [hrm_eq] at hs
  by_cases hemp:sl.vMap.isEmpty = true
  · rw [if_pos hemp] at hbranch
    simp only [Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at hbranch
    obtain ⟨hLle,hall⟩:=hbranch
    have hnd:orVars.Nodup:=(List.nodup_range).filter _
    have hess:∀ v ∈ orVars,v < n /\
        ∃ k1 k2,k1 < 1 <<< n /\ k2 < 1 <<< n /\ (maskSub n sl.zM sl.oM).testBit k1 = true /\
          (maskSub n sl.zM sl.oM).testBit k2 = true /\
          (∀ j < n,j ≠ v -> k1.testBit j = k2.testBit j) /\ tgt.testBit k1 ≠ tgt.testBit k2:=by
      intro v hv
      have hvn:v < n:=List.mem_range.1 (List.mem_filter.1 hv).1
      refine ⟨hvn,?_⟩
      have h1:=hall v hv
      rw [hrm_eq] at h1
      exact isEssOn_sound n (maskSub n sl.zM sl.oM) tgt v hvn h1
    have hlb:=lower_essential n (maskSub n sl.zM sl.oM) tgt s orVars hnd hess hs
    omega
  · rw [if_neg hemp] at hbranch
    simp only [Bool.and_eq_true,List.all_eq_true] at hbranch
    obtain ⟨⟨hzo0,hforce_all⟩,htail⟩:=hbranch
    have hfold_bits:∀ L:List ℕ,∀ acc i,
        (L.foldl (fun a v => a ||| (1 <<< v)) acc).testBit i = (acc.testBit i || L.any (fun v => decide (v = i))):=by
      intro L
      induction L with
      | nil => intro acc i; simp
      | cons v L ih =>
        intro acc i
        simp only [List.foldl_cons,List.any_cons,ih,Nat.testBit_or,testBit_one_shiftLeft,Bool.or_assoc,eq_comm]
    have hor_eq:orVars.foldl (fun a v => a ||| (1 <<< v)) 0 = sl.orM:=by
      apply Nat.eq_of_testBit_eq; intro i
      rw [hfold_bits]; simp only [Nat.zero_testBit,Bool.false_or]
      by_cases hin:i < n
      · cases hb:sl.orM.testBit i with
        | true =>
          rw [List.any_eq_true]
          exact ⟨i,List.mem_filter.2 ⟨List.mem_range.2 hin,hb⟩,by simp⟩
        | false =>
          rw [List.any_eq_false]
          intro v hv
          simp only [decide_eq_true_eq]
          intro hvi; subst hvi
          have:=(List.mem_filter.1 hv).2; rw [hb] at this; cases this
      · have hzero:sl.orM.testBit i = false:=by
          apply Nat.testBit_lt_two_pow
          have:1 <<< n ≤ 2 ^ i:=by
            simp only [Nat.shiftLeft_eq,Nat.one_mul]
            exact Nat.pow_le_pow_right (by omega) (by omega)
          omega
        rw [hzero,List.any_eq_false]
        intro v hv
        have hvn:=List.mem_range.1 (List.mem_filter.1 hv).1
        simp [show v ≠ i by omega]
    have hzo_ex:∃ z1 o1,z1 < 1 <<< n /\ o1 < 1 <<< n /\
        rm0.testBit z1 = true /\ rm0.testBit o1 = true /\
        tgt.testBit z1 = false /\ tgt.testBit o1 = true:=by
      simp only [hasZeroAndOne,Bool.and_eq_true,List.any_eq_true,List.mem_range,Bool.not_eq_true'] at hzo0
      obtain ⟨⟨z1,hz1,hrz,htz⟩,⟨o1,ho1,hro,hto⟩⟩:=hzo0
      exact ⟨z1,o1,hz1,ho1,hrz,hro,htz,hto⟩
    have hpeel:=peel_or_vars n sl.zM sl.oM tgt orVars sl.zM s
      (by
        intro v hv
        obtain ⟨hvn,horv⟩:=List.mem_filter.1 hv
        rw [List.mem_range] at hvn
        have hzv:sl.zM.testBit v = false:=by
          have:=congrArg (fun x => x.testBit v) hdisj_z
          simp [Nat.testBit_and,horv] at this; exact this
        have hov:sl.oM.testBit v = false:=by
          have:=congrArg (fun x => x.testBit v) hdisj_o
          simp [Nat.testBit_and,horv] at this; exact this
        refine ⟨hvn,hzv,hov,fun k hk hrmk hkv => ?_⟩
        have hf:=hforce_all v hv k (List.mem_range.2 hk)
        rw [hrm_eq] at hf
        simpa [hrmk,hkv] using hf)
      ((List.nodup_range).filter _)
      (by simpa [hor_eq,rm0] using hzo_ex)
      hs
    rw [hor_eq] at hpeel
    obtain ⟨hpeel_le,hs0⟩:=hpeel
    by_cases hbid:sl.baseId < bases.size
    · simp only [hbid,↓reduceDIte,Bool.and_eq_true,decide_eq_true_eq] at htail
      obtain ⟨⟨hLle,hemb⟩,hzo_b⟩:=htail
      set bm:=(bases[sl.baseId]).1
      set bTgt:=(bases[sl.baseId]).2.1
      set bL:=(bases[sl.baseId]).2.2
      simp only [checkEmbed,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,List.all_eq_true,List.mem_range,Bool.not_eq_true'] at hemb
      obtain ⟨⟨⟨hvmlen,hvmnd⟩,hvmdisj⟩,hvmemb⟩:=hemb
      have hiso:=iso_bound n bm rm0 tgt bTgt sl.oM (s - orVars.length) sl.vMap
        hvmlen hvmnd (fun i hi => hvmdisj i hi)
        (fun k hk => by
          have hk':=hvmemb k hk
          exact ⟨hk'.1.1,hk'.1.2,hk'.2⟩)
        (by
          obtain ⟨z1,o1,hz1,ho1,_,_,hne⟩:=hasZeroAndOne_sound bm (maskN bm) bTgt hzo_b
          exact ⟨z1,o1,hz1,ho1,hne⟩)
        hs0
      have hblb:bL ≤ s - orVars.length:=hbases sl.baseId hbid (s - orVars.length) hiso
      omega
    · simp only [hbid,↓reduceDIte,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at htail
      obtain ⟨⟨hLle,hvmnd⟩,hvmess⟩:=htail
      have hlb:=lower_essential n rm0 tgt (s - orVars.length) sl.vMap hvmnd
        (fun v hv => by
          have h1:=hvmess v hv
          exact ⟨h1.1,isEssOn_sound n rm0 tgt v h1.1 h1.2⟩)
        hs0
      omega
end PEqualNP.Outside.L_meta_10650_aux
namespace PEqualNP.Outside.L_meta_10650_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def normW (full w:ℕ):ℕ :=
  if w.testBit 0 then w ^^^ full else w
def applyOp (full op a b:ℕ):ℕ :=
  match op with
  | 0 => normW full (a &&& b)
  | 1 => normW full (a ||| b)
  | 2 => normW full (a &&& (b ^^^ full))
  | _ => normW full ((a ^^^ full) &&& b)
theorem testBit_normW (full w k:ℕ) (h0:full.testBit 0 = true) (hk:full.testBit k = true) :
    (normW full w).testBit k = xor (w.testBit k) (w.testBit 0):=by
  unfold normW
  cases h:w.testBit 0 <;> simp [Nat.testBit_xor,hk]
theorem normW_bit0 (full w:ℕ) (h0:full.testBit 0 = true) :
    (normW full w).testBit 0 = false:=by
  rw [testBit_normW full w 0 h0 h0]; cases w.testBit 0 <;> rfl
theorem normW_of_bit0_false (full w:ℕ) (h:w.testBit 0 = false) :
    normW full w = w:=by
  simp [normW,h]
theorem normW_xor_full (full w:ℕ) (h0:full.testBit 0 = true) (hw:w &&& full = w) :
    normW full (w ^^^ full) = normW full w:=by
  apply Nat.eq_of_testBit_eq; intro k
  have hwk:w.testBit k = true -> full.testBit k = true:=by
    intro h; have:=congrArg (fun x => x.testBit k) hw
    simp [Nat.testBit_and,h] at this; exact this
  by_cases hfk:full.testBit k = true
  · rw [testBit_normW full (w ^^^ full) k h0 hfk,testBit_normW full w k h0 hfk]
    simp only [Nat.testBit_xor,h0,hfk]
    cases w.testBit k <;> cases w.testBit 0 <;> rfl
  · have hfk':full.testBit k = false:=Bool.eq_false_iff.2 hfk
    have hwk':w.testBit k = false:=by
      cases hb:w.testBit k
      · rfl
      · exfalso; exact hfk (hwk hb)
    unfold normW
    simp only [Nat.testBit_xor,h0]
    cases w.testBit 0 <;> simp [Nat.testBit_xor,hfk',hwk']
theorem normW_le_mask (n w:ℕ) (hw:w &&& maskN n = w) :
    normW (maskN n) w &&& maskN n = normW (maskN n) w:=by
  apply Nat.eq_of_testBit_eq; intro k
  have hwk:=congrArg (fun x => x.testBit k) hw
  simp only [Nat.testBit_and] at hwk ⊢
  unfold normW
  cases w.testBit 0 with
  | false => exact hwk
  | true =>
    simp only [↓reduceIte,Nat.testBit_xor,Nat.testBit_and]
    cases hmk:(maskN n).testBit k <;> simp [hmk] at hwk ⊢
    exact hwk
theorem applyOp_swap (full op a b:ℕ) (hop:op < 4) :
    applyOp full (match op with | 2 => 3 | 3 => 2 | _ => op) b a = applyOp full op a b:=by
  rcases op with _ | _ | _ | _ | op
  · simp [applyOp,Nat.and_comm]
  · simp [applyOp,Nat.or_comm]
  · simp [applyOp,Nat.and_comm]
  · simp [applyOp,Nat.and_comm]
  · omega
theorem normW_sOpEval (n op:ℕ) (a b:ℕ)
    (ha:a &&& maskN n = a) (hb:b &&& maskN n = b) :
    ∃ op' < 4,
      normW (maskN n) (encB n (fun k => sOpEval op (a.testBit k) (b.testBit k))) =
      applyOp (maskN n) op' (normW (maskN n) a) (normW (maskN n) b):=by
  have h0:(maskN n).testBit 0 = true:=by
    rw [testBit_maskN]; simp [Nat.shiftLeft_eq]
  have hbit_eq:∀ op',
      (∀ k < 1 <<< n,
        xor (sOpEval op (a.testBit k) (b.testBit k)) (sOpEval op (a.testBit 0) (b.testBit 0)) =
        xor (sOpEval op' (xor (a.testBit k) (a.testBit 0)) (xor (b.testBit k) (b.testBit 0)))
            (sOpEval op' false false)) ->
      normW (maskN n) (encB n (fun k => sOpEval op (a.testBit k) (b.testBit k))) =
      applyOp (maskN n) op' (normW (maskN n) a) (normW (maskN n) b):=by
    intro op' hpt
    apply Nat.eq_of_testBit_eq; intro k
    by_cases hk:k < 1 <<< n
    · have hmk:(maskN n).testBit k = true:=by rw [testBit_maskN]; simp [hk]
      have h0lt:0 < 1 <<< n:=by simp [Nat.shiftLeft_eq]
      rw [testBit_normW (maskN n) _ k h0 hmk,encB_testBit,encB_testBit]
      simp only [hk,h0lt,decide_true,Bool.true_and]
      rw [hpt k hk]
      have hna:=testBit_normW (maskN n) a k h0 hmk
      have hnb:=testBit_normW (maskN n) b k h0 hmk
      have hna0:=normW_bit0 (maskN n) a h0
      have hnb0:=normW_bit0 (maskN n) b h0
      rcases op' with _ | _ | _ | op' <;>
        simp only [applyOp,testBit_normW (maskN n) _ k h0 hmk,Nat.testBit_and,Nat.testBit_or,
          Nat.testBit_xor,hmk,h0,hna,hnb,hna0,hnb0,sOpEval] <;>
        cases (a.testBit k ^^ a.testBit 0) <;> cases (b.testBit k ^^ b.testBit 0) <;> rfl
    · have hmk:(maskN n).testBit k = false:=by rw [testBit_maskN]; simp [hk]
      have ha':a.testBit k = false:=by
        have:=congrArg (fun x => x.testBit k) ha; simp [Nat.testBit_and,hmk] at this; exact this
      have hb':b.testBit k = false:=by
        have:=congrArg (fun x => x.testBit k) hb; simp [Nat.testBit_and,hmk] at this; exact this
      have hna':(normW (maskN n) a).testBit k = false:=by
        unfold normW; cases a.testBit 0 <;> simp [Nat.testBit_xor,ha',hmk]
      have hnb':(normW (maskN n) b).testBit k = false:=by
        unfold normW; cases b.testBit 0 <;> simp [Nat.testBit_xor,hb',hmk]
      have hlhs:(normW (maskN n) (encB n (fun k => sOpEval op (a.testBit k) (b.testBit k)))).testBit k = false:=by
        unfold normW
        cases (encB n (fun k => sOpEval op (a.testBit k) (b.testBit k))).testBit 0 <;>
          simp [Nat.testBit_xor,encB_testBit,hk,hmk]
      rw [hlhs]
      symm
      set na:=normW (maskN n) a
      set nb:=normW (maskN n) b
      have hna'':na.testBit k = false:=hna'
      have hnb'':nb.testBit k = false:=hnb'
      rcases op' with _ | _ | _ | op' <;>
      · unfold applyOp normW
        split_ifs <;> simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,hna'',hnb'',hmk] <;> rfl
  rcases op with _ | _ | _ | op <;> cases ha0:a.testBit 0 <;> cases hb0:b.testBit 0
  · exact ⟨0,by omega,hbit_eq 0 (fun k _ => by simp only [ha0,hb0]; cases a.testBit k <;> cases b.testBit k <;> rfl)⟩
  · exact ⟨2,by omega,hbit_eq 2 (fun k _ => by simp only [ha0,hb0]; cases a.testBit k <;> cases b.testBit k <;> rfl)⟩
  · exact ⟨3,by omega,hbit_eq 3 (fun k _ => by simp only [ha0,hb0]; cases a.testBit k <;> cases b.testBit k <;> rfl)⟩
  · exact ⟨1,by omega,hbit_eq 1 (fun k _ => by simp only [ha0,hb0]; cases a.testBit k <;> cases b.testBit k <;> rfl)⟩
  · exact ⟨1,by omega,hbit_eq 1 (fun k _ => by simp only [ha0,hb0]; cases a.testBit k <;> cases b.testBit k <;> rfl)⟩
  · exact ⟨3,by omega,hbit_eq 3 (fun k _ => by simp only [ha0,hb0]; cases a.testBit k <;> cases b.testBit k <;> rfl)⟩
  · exact ⟨2,by omega,hbit_eq 2 (fun k _ => by simp only [ha0,hb0]; cases a.testBit k <;> cases b.testBit k <;> rfl)⟩
  · exact ⟨0,by omega,hbit_eq 0 (fun k _ => by simp only [ha0,hb0]; cases a.testBit k <;> cases b.testBit k <;> rfl)⟩
  · exact ⟨2,by omega,hbit_eq 2 (fun k _ => by simp only [ha0,hb0]; cases a.testBit k <;> cases b.testBit k <;> rfl)⟩
  · exact ⟨0,by omega,hbit_eq 0 (fun k _ => by simp only [ha0,hb0]; cases a.testBit k <;> cases b.testBit k <;> rfl)⟩
  · exact ⟨1,by omega,hbit_eq 1 (fun k _ => by simp only [ha0,hb0]; cases a.testBit k <;> cases b.testBit k <;> rfl)⟩
  · exact ⟨3,by omega,hbit_eq 3 (fun k _ => by simp only [ha0,hb0]; cases a.testBit k <;> cases b.testBit k <;> rfl)⟩
  · exact ⟨3,by omega,hbit_eq 3 (fun k _ => by simp only [ha0,hb0]; cases a.testBit k <;> cases b.testBit k <;> rfl)⟩
  · exact ⟨1,by omega,hbit_eq 1 (fun k _ => by simp only [ha0,hb0]; cases a.testBit k <;> cases b.testBit k <;> rfl)⟩
  · exact ⟨0,by omega,hbit_eq 0 (fun k _ => by simp only [ha0,hb0]; cases a.testBit k <;> cases b.testBit k <;> rfl)⟩
  · exact ⟨2,by omega,hbit_eq 2 (fun k _ => by simp only [ha0,hb0]; cases a.testBit k <;> cases b.testBit k <;> rfl)⟩
def mkCand (ws:List ℕ) (a b z:ℕ) (kc:ℕ):List ℕ :=
  let base:=(ws.erase a).erase b ++ [z]
  match kc with
  | 0 => base
  | 1 => base ++ [a]
  | 2 => base ++ [b]
  | _ => base ++ [a,b]
inductive SRun (full tgt:ℕ):ℕ -> List ℕ -> Prop
  | done (s:ℕ):SRun full tgt s [tgt]
  | perm {s:ℕ} {ws ws':List ℕ}:ws.Perm ws' -> SRun full tgt s ws -> SRun full tgt s ws'
  | step (s:ℕ) (ws:List ℕ) (a b op kc:ℕ) :
      ws.Nodup -> a ∈ ws -> b ∈ ws -> a ≠ b -> op < 4 -> kc < 4 ->
      applyOp full op a b ≠ 0 ->
      applyOp full op a b ≠ full ->
      applyOp full op a b ∉ ws ->
      (mkCand ws a b (applyOp full op a b) kc).length ≤ s + 1 ->
      SRun full tgt s (mkCand ws a b (applyOp full op a b) kc) ->
      SRun full tgt (s + 1) ws
theorem mkCand_nodup {ws:List ℕ} {a b z kc:ℕ}
    (hnd:ws.Nodup) (ha:a ∈ ws) (hb:b ∈ ws) (hab:a ≠ b) (hz:z ∉ ws) :
    (mkCand ws a b z kc).Nodup:=by
  have h1:(ws.erase a).Nodup:=hnd.erase a
  have h2:((ws.erase a).erase b).Nodup:=h1.erase b
  have hna:a ∉ (ws.erase a).erase b:=fun h => hnd.not_mem_erase (List.mem_of_mem_erase h)
  have hnb:b ∉ (ws.erase a).erase b:=h1.not_mem_erase
  have hnz:z ∉ (ws.erase a).erase b:=fun h => hz (List.mem_of_mem_erase (List.mem_of_mem_erase h))
  have hza:z ≠ a:=fun h => hz (h ▸ ha)
  have hzb:z ≠ b:=fun h => hz (h ▸ hb)
  have hbase_nd:((ws.erase a).erase b ++ [z]).Nodup:=by
    rw [List.nodup_append]
    exact ⟨h2,List.nodup_singleton z,fun x hx y hy => by
      simp only [List.mem_singleton] at hy; subst hy
      intro heq; exact hnz (heq ▸ hx)⟩
  rcases kc with _ | _ | _ | kc
  · exact hbase_nd
  · rw [mkCand,List.nodup_append]
    exact ⟨hbase_nd,List.nodup_singleton a,fun x hx y hy => by
      simp only [List.mem_singleton] at hy; subst hy
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hx | rfl
      · intro heq; exact hna (heq ▸ hx)
      · exact hza⟩
  · rw [mkCand,List.nodup_append]
    exact ⟨hbase_nd,List.nodup_singleton b,fun x hx y hy => by
      simp only [List.mem_singleton] at hy; subst hy
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hx | rfl
      · intro heq; exact hnb (heq ▸ hx)
      · exact hzb⟩
  · simp only [mkCand]
    rw [List.nodup_append]
    refine ⟨hbase_nd,List.nodup_cons.2 ⟨by simp [hab],List.nodup_singleton b⟩,fun x hx y hy => ?_⟩
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx hy
    rcases hx with hx | rfl <;> rcases hy with rfl | rfl
    · intro heq; exact hna (heq ▸ hx)
    · intro heq; exact hnb (heq ▸ hx)
    · exact hza
    · exact hzb
theorem mkCand_subset {ws:List ℕ} {a b z kc:ℕ} (ha:a ∈ ws) (hb:b ∈ ws) :
    ∀ w ∈ mkCand ws a b z kc,w = z \/ w ∈ ws:=by
  intro w hw
  rcases kc with _ | _ | _ | kc <;> simp only [mkCand,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
  · rcases hw with h | rfl
    · exact Or.inr (List.mem_of_mem_erase (List.mem_of_mem_erase h))
    · exact Or.inl rfl
  · rcases hw with (h | rfl) | rfl
    · exact Or.inr (List.mem_of_mem_erase (List.mem_of_mem_erase h))
    · exact Or.inl rfl
    · exact Or.inr ha
  · rcases hw with (h | rfl) | rfl
    · exact Or.inr (List.mem_of_mem_erase (List.mem_of_mem_erase h))
    · exact Or.inl rfl
    · exact Or.inr hb
  · rcases hw with (h | rfl) | (rfl | rfl)
    · exact Or.inr (List.mem_of_mem_erase (List.mem_of_mem_erase h))
    · exact Or.inl rfl
    · exact Or.inr ha
    · exact Or.inr hb
theorem mkCand_swap {ws:List ℕ} {a b z kc:ℕ} (hab:a ≠ b) :
    (mkCand ws b a z (match kc with | 1 => 2 | 2 => 1 | _ => kc)).Perm (mkCand ws a b z kc):=by
  have her:(ws.erase b).erase a = (ws.erase a).erase b:=List.erase_comm (l:=ws) b a
  rcases kc with _ | _ | _ | kc <;> simp only [mkCand,her]
  · exact List.Perm.refl _
  · exact List.Perm.refl _
  · exact List.Perm.refl _
  · exact List.Perm.append_left _ (List.Perm.swap a b [])
theorem sSubst_delete_gate (n:ℕ) (sgs:List SGate) (p:ℕ) (g:SGate)
    (hcl:SCleanL n sgs) (hp:sgs[p]? = some g) (rep:SStat)
    (hrep_v:sStatValid (n + p) rep)
    (hrep_val:∀ k < 1 <<< n,
      sStatVal (sWiresFrom (sgs.take p) (List.ofFn (pt n k))) rep =
      (sWiresFrom sgs (List.ofFn (pt n k))).getD (n + p) false)
    (o:ℕ) (pol:Bool) (ho:o < n + sgs.length) (tgt:ℕ)
    (hev:∀ k < 1 <<< n,xor ((sWiresFrom sgs (List.ofFn (pt n k))).getD o false) pol = tgt.testBit k)
    (hnc:∃ z1 o1,z1 < 1 <<< n /\ o1 < 1 <<< n /\ tgt.testBit z1 ≠ tgt.testBit o1) :
    HasSignedOn n (maskN n) tgt (sgs.length - 1):=by
  obtain ⟨pre,post,hsgs,hplen⟩:=split_at sgs p g hp
  have htake:sgs.take p = pre:=by rw [hsgs,List.take_left' hplen]
  rw [htake] at hrep_val
  set init:List SStat:=(List.range (n + p)).map (fun i => Sum.inr (i,false)) ++ [rep]
  set res:=sSubst n post (init,pre)
  have hinit_len:init.length = n + p + 1:=by simp [init]
  have hinit_get:∀ i,init.getD i (Sum.inl false) =
      if i < n + p then Sum.inr (i,false) else if i = n + p then rep else Sum.inl false:=by
    intro i
    by_cases hlt:i < n + p
    · rw [List.getD_append _ _ _ _ (by simp; omega)]
      simp [hlt,List.getD_eq_getElem?_getD]
    · by_cases heq:i = n + p
      · subst heq
        rw [getD_snoc_len _ _ _ _ (by simp)]
        simp
      · rw [List.getD_eq_default _ _ (by simp [init]; omega)]
        simp [hlt,heq]
  have hcl_pre:SCleanL n pre:=by
    intro q g' hq
    have hq':sgs[q]? = some g':=by
      have hqlt:q < pre.length:=(List.getElem?_eq_some_iff.1 hq).1
      rw [hsgs,List.getElem?_append_left hqlt]; exact hq
    exact hcl q g' hq'
  have hcl':SCleanL n res.2:=by
    apply sSubst_clean n post (init,pre)
    · intro i; rw [hinit_get,hplen]
      split_ifs with h1 h2
      · exact h1
      · exact hrep_v
      · trivial
    · exact hcl_pre
  have hlen':res.2.length ≤ sgs.length - 1:=by
    have h1:res.2.length ≤ pre.length + post.length:=sSubst_len n post (init,pre)
    rw [hsgs]; simp only [List.length_append,List.length_cons]; omega
  have hinv:∀ k < 1 <<< n,
      SInv n (List.ofFn (pt n k)) (sWiresFrom sgs (List.ofFn (pt n k))) res:=by
    intro k hk
    have hwf:sWiresFrom sgs (List.ofFn (pt n k)) =
        sWiresFrom post (sWiresFrom pre (List.ofFn (pt n k)) ++
          [sOpEval g.op ((sWiresFrom pre (List.ofFn (pt n k))).getD g.a false)
                       ((sWiresFrom pre (List.ofFn (pt n k))).getD g.b false)]):=by
      rw [hsgs,sWiresFrom_append]; rfl
    rw [hwf]
    apply sInv_subst n (List.ofFn (pt n k)) (by simp) post _ (init,pre)
    have hpre_wlen:(sWiresFrom pre (List.ofFn (pt n k))).length = n + p:=by
      rw [length_sWiresFrom,List.length_ofFn,hplen]
    refine ⟨by simp [hinit_len,hpre_wlen],fun i => ?_⟩
    rw [hinit_get,hplen]
    by_cases hlt:i < n + p
    · simp only [hlt,↓reduceIte,sStatValid,sStatVal,Bool.xor_false,true_and]
      rw [List.getD_append _ _ _ _ (by omega)]
    · by_cases heq:i = n + p
      · subst heq
        simp only [lt_irrefl,↓reduceIte,hrep_v,true_and]
        rw [getD_snoc_len _ _ _ _ hpre_wlen,hrep_val k hk]
        rw [hsgs,sWiresFrom_append]
        have hstep:sWiresFrom (g :: post) (sWiresFrom pre (List.ofFn (pt n k))) =
            sWiresFrom post (sWiresFrom pre (List.ofFn (pt n k)) ++
              [sOpEval g.op ((sWiresFrom pre (List.ofFn (pt n k))).getD g.a false)
                           ((sWiresFrom pre (List.ofFn (pt n k))).getD g.b false)]):=rfl
        rw [hstep,getD_sWiresFrom post _ (n + p) (by simp [hpre_wlen]),getD_snoc_len _ _ _ _ hpre_wlen]
      · simp only [hlt,heq,↓reduceIte,sStatValid,sStatVal,true_and]
        rw [List.getD_eq_default _ _ (by simp [hpre_wlen]; omega)]
  cases hsto:res.1.getD o (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨z1,o1,hz1,ho1,hne⟩:=hnc
    have h1:=((hinv z1 hz1).2 o).2; rw [hsto] at h1
    have h2:=((hinv o1 ho1).2 o).2; rw [hsto] at h2
    have e1:=hev z1 hz1; have e2:=hev o1 ho1
    simp only [sStatVal] at h1 h2
    rw [<- h1] at e1; rw [<- h2] at e2
    exact hne (e1.symm.trans e2)
  | inr pair =>
    obtain ⟨o',p'⟩:=pair
    obtain ⟨z1,_,hz1,_,_⟩:=hnc
    have ho':o' < n + res.2.length:=by
      have:=((hinv z1 hz1).2 o).1; rwa [hsto] at this
    refine ⟨res.2,o',xor p' pol,hcl',hlen',ho',fun k hk _ => ?_⟩
    have h1:=((hinv k hk).2 o).2; rw [hsto] at h1
    simp only [sStatVal] at h1
    have e1:=hev k hk
    rw [<- e1,<- h1]
    cases ((sWiresFrom res.2 (List.ofFn (pt n k))).getD o' false) <;> cases p' <;> cases pol <;> rfl
def sLiveBack (n:ℕ) (sgs:List SGate) (o:ℕ):ℕ -> List ℕ
  | 0 => [o]
  | r + 1 =>
    let p:=sgs.length - 1 - r
    match sgs[p]? with
    | some g => sLiveStep n p g (sLiveBack n sgs o r)
    | none   => sLiveBack n sgs o r
theorem sLiveStep_nodup (n p:ℕ) (g:SGate) (L:List ℕ) (hnd:L.Nodup) :
    (sLiveStep n p g L).Nodup:=by
  unfold sLiveStep
  by_cases h1:n + p ∈ L
  · simp only [h1,↓reduceIte]
    have hnd1:(L.filter (· != n + p)).Nodup:=hnd.filter _
    set L1:=L.filter (· != n + p)
    have hnd2:(if g.a ∈ L1 then L1 else g.a :: L1).Nodup:=by
      split_ifs with ha
      · exact hnd1
      · exact List.nodup_cons.2 ⟨ha,hnd1⟩
    set L2:=if g.a ∈ L1 then L1 else g.a :: L1
    split_ifs with hb
    · exact hnd2
    · exact List.nodup_cons.2 ⟨hb,hnd2⟩
  · simp only [h1,↓reduceIte]; exact hnd
theorem sLiveBack_nodup (n:ℕ) (sgs:List SGate) (o:ℕ) :
    ∀ r,(sLiveBack n sgs o r).Nodup:=by
  intro r
  induction r with
  | zero => simp [sLiveBack]
  | succ r ih =>
    simp only [sLiveBack]
    cases sgs[sgs.length - 1 - r]? with
    | none => exact ih
    | some g => exact sLiveStep_nodup n _ g _ ih
theorem sLiveBack_length (n:ℕ) (sgs:List SGate) (o:ℕ) :
    ∀ r,(sLiveBack n sgs o r).length ≤ r + 1:=by
  intro r
  induction r with
  | zero => simp [sLiveBack]
  | succ r ih =>
    simp only [sLiveBack]
    cases sgs[sgs.length - 1 - r]? with
    | none => simp only; omega
    | some g =>
      simp only
      have:=sLiveStep_length n (sgs.length - 1 - r) g (sLiveBack n sgs o r)
      omega
theorem sLiveBack_lt (n:ℕ) (sgs:List SGate) (hcl:SCleanL n sgs) (o:ℕ) (ho:o < n + sgs.length) :
    ∀ r ≤ sgs.length,∀ u ∈ sLiveBack n sgs o r,u < n + (sgs.length - r):=by
  intro r
  induction r with
  | zero => intro _ u hu; simp [sLiveBack] at hu; subst hu; exact ho
  | succ r ih =>
    intro hr u hu
    have hplt:sgs.length - 1 - r < sgs.length:=by omega
    have hget:sgs[sgs.length - 1 - r]? = some sgs[sgs.length - 1 - r]:=List.getElem?_eq_getElem hplt
    simp only [sLiveBack,hget] at hu
    obtain ⟨hga,hgb,_⟩:=hcl _ _ hget
    have hprev:∀ v ∈ sLiveBack n sgs o r,v < n + ((sgs.length - 1 - r) + 1):=by
      intro v hv
      have:=ih (by omega) v hv
      omega
    have hstep:=sLiveStep_lt n (sgs.length - 1 - r) sgs[sgs.length - 1 - r] _ hprev hga hgb u hu
    omega
theorem sSubst_delete_dead (n:ℕ) (sgs:List SGate) (p:ℕ) (g:SGate)
    (hcl:SCleanL n sgs) (hp:sgs[p]? = some g)
    (o:ℕ) (pol:Bool) (ho:o < n + sgs.length) (tgt:ℕ)
    (hev:∀ k < 1 <<< n,xor ((sWiresFrom sgs (List.ofFn (pt n k))).getD o false) pol = tgt.testBit k)
    (hdead:(n + p) ∉ sLiveBack n sgs o (sgs.length - (p + 1)))
    (hnc:∃ z1 o1,z1 < 1 <<< n /\ o1 < 1 <<< n /\ tgt.testBit z1 ≠ tgt.testBit o1) :
    HasSignedOn n (maskN n) tgt (sgs.length - 1):=by
  obtain ⟨pre,post,hsgs,hplen⟩:=split_at sgs p g hp
  have hp_lt:p < sgs.length:=(List.getElem?_eq_some_iff.1 hp).1
  set init:List SStat:=(List.range (n + p)).map (fun i => Sum.inr (i,false)) ++ [Sum.inl false]
  set res:=sSubst n post (init,pre)
  have hinit_len:init.length = n + p + 1:=by simp [init]
  have hinit_get:∀ i,init.getD i (Sum.inl false) =
      if i < n + p then Sum.inr (i,false) else Sum.inl false:=by
    intro i
    by_cases hlt:i < n + p
    · rw [List.getD_append _ _ _ _ (by simp; omega)]
      simp [hlt,List.getD_eq_getElem?_getD]
    · by_cases heq:i = n + p
      · subst heq; rw [getD_snoc_len _ _ _ _ (by simp)]; simp
      · rw [List.getD_eq_default _ _ (by simp [init]; omega)]; simp [hlt]
  have hcl_pre:SCleanL n pre:=by
    intro q g' hq
    have hqlt:q < pre.length:=(List.getElem?_eq_some_iff.1 hq).1
    exact hcl q g' (by rw [hsgs,List.getElem?_append_left hqlt]; exact hq)
  have hcl':SCleanL n res.2:=by
    apply sSubst_clean n post (init,pre)
    · intro i; rw [hinit_get,hplen]; split_ifs with h1; exact h1; trivial
    · exact hcl_pre
  have hlen':res.2.length ≤ sgs.length - 1:=by
    have h1:res.2.length ≤ pre.length + post.length:=sSubst_len n post (init,pre)
    rw [hsgs]; simp only [List.length_append,List.length_cons]; omega
  have hinv_fake:∀ k < 1 <<< n,
      SInv n (List.ofFn (pt n k)) (sWiresFrom post (sWiresFrom pre (List.ofFn (pt n k)) ++ [false])) res:=by
    intro k hk
    apply sInv_subst n (List.ofFn (pt n k)) (by simp) post _ (init,pre)
    have hpre_wlen:(sWiresFrom pre (List.ofFn (pt n k))).length = n + p:=by
      rw [length_sWiresFrom,List.length_ofFn,hplen]
    refine ⟨by simp [hinit_len,hpre_wlen],fun i => ?_⟩
    rw [hinit_get,hplen]
    by_cases hlt:i < n + p
    · simp only [hlt,↓reduceIte,sStatValid,sStatVal,Bool.xor_false,true_and]
      rw [List.getD_append _ _ _ _ (by omega)]
    · by_cases heq:i = n + p
      · subst heq
        simp only [lt_irrefl,↓reduceIte,sStatValid,sStatVal,true_and]
        rw [getD_snoc_len _ _ _ _ hpre_wlen]
      · simp only [hlt,↓reduceIte,sStatValid,sStatVal,true_and]
        rw [List.getD_eq_default _ _ (by simp [hpre_wlen]; omega)]
  have hagree:∀ k < 1 <<< n,∀ r ≤ sgs.length - (p + 1),
      ∀ u ∈ sLiveBack n sgs o r,
        (sWiresFrom post (sWiresFrom pre (List.ofFn (pt n k)) ++ [false])).getD u false =
        (sWiresFrom sgs (List.ofFn (pt n k))).getD u false:=by
    intro k hk
    suffices key:∀ d ≤ sgs.length - (p + 1),
        ∀ u ∈ sLiveBack n sgs o (sgs.length - (p + 1) - d),
          (sWiresFrom post (sWiresFrom pre (List.ofFn (pt n k)) ++ [false])).getD u false =
          (sWiresFrom sgs (List.ofFn (pt n k))).getD u false by
      intro r hr
      have:sgs.length - (p + 1) - (sgs.length - (p + 1) - r) = r:=by omega
      rw [<- this]
      exact key (sgs.length - (p + 1) - r) (by omega)
    intro d
    induction d with
    | zero =>
      intro _ u hu
      simp only [Nat.sub_zero] at hu
      have hult:=sLiveBack_lt n sgs hcl o ho (sgs.length - (p + 1)) (by omega) u hu
      have hune:u ≠ n + p:=fun h => hdead (h ▸ hu)
      have hlt:u < n + p:=by omega
      have hpre_wlen:(sWiresFrom pre (List.ofFn (pt n k))).length = n + p:=by
        rw [length_sWiresFrom,List.length_ofFn,hplen]
      rw [getD_sWiresFrom post _ u (by simp [hpre_wlen]; omega),
          List.getD_append _ _ _ _ (by omega)]
      rw [hsgs,sWiresFrom_append,getD_sWiresFrom (g :: post) _ u (by omega)]
    | succ d ih =>
      intro hd u hu
      set r:=sgs.length - (p + 1) - (d + 1)
      have hr1:sgs.length - (p + 1) - d = r + 1:=by omega
      have hq:sgs.length - 1 - r = p + 1 + d:=by omega
      have hqlt:p + 1 + d < sgs.length:=by omega
      have hget:sgs[p + 1 + d]? = some sgs[p + 1 + d]:=List.getElem?_eq_getElem hqlt
      have hprev:=ih (by omega)
      rw [hr1] at hprev
      simp only [sLiveBack,hq,hget] at hprev
      obtain ⟨hga,hgb,_⟩:=hcl _ _ hget
      by_cases huq:u = n + (p + 1 + d)
      · subst huq
        have hmemL:n + (p + 1 + d) ∈ sLiveBack n sgs o r:=hu
        set L':=sLiveStep n (p + 1 + d) sgs[p + 1 + d] (sLiveBack n sgs o r)
        have hga_m:sgs[p + 1 + d].a ∈ L':=by
          unfold L' sLiveStep; simp only [hmemL,↓reduceIte]
          set L1:=(sLiveBack n sgs o r).filter (· != n + (p + 1 + d))
          set L2:=if sgs[p + 1 + d].a ∈ L1 then L1 else sgs[p + 1 + d].a :: L1
          have hm2:sgs[p + 1 + d].a ∈ L2:=by dsimp only [L2]; split_ifs with h <;> simp [h]
          by_cases hb:sgs[p + 1 + d].b ∈ L2
          · simp [hb,hm2]
          · simp [hb,hm2]
        have hgb_m:sgs[p + 1 + d].b ∈ L':=by
          unfold L' sLiveStep; simp only [hmemL,↓reduceIte]
          set L1:=(sLiveBack n sgs o r).filter (· != n + (p + 1 + d))
          set L2:=if sgs[p + 1 + d].a ∈ L1 then L1 else sgs[p + 1 + d].a :: L1
          by_cases hb:sgs[p + 1 + d].b ∈ L2 <;> simp [hb]
        have hpost_q:post[d]? = some sgs[p + 1 + d]:=by
          set g1:=sgs[p + 1 + d]
          have h1:sgs[p + 1 + d]? = some g1:=hget
          rw [hsgs,List.getElem?_append_right (by omega)] at h1
          have:p + 1 + d - pre.length = d + 1:=by omega
          rw [this] at h1
          simpa using h1
        have hpre_wlen:(sWiresFrom pre (List.ofFn (pt n k)) ++ [false]).length = n + p + 1:=by
          rw [List.length_append,length_sWiresFrom,List.length_ofFn,hplen]; simp
        have heq_idx:n + (p + 1 + d) = (n + p + 1) + d:=by omega
        rw [sWiresFrom_getD_gate n sgs (p + 1 + d) sgs[p + 1 + d] hget hga hgb _ (by simp)]
        rw [heq_idx,sWiresFrom_getD_gate (n + p + 1) post d sgs[p + 1 + d] hpost_q (by omega) (by omega) _ hpre_wlen]
        rw [hprev _ hga_m,hprev _ hgb_m]
      · apply hprev u
        unfold sLiveStep
        by_cases hmemL:n + (p + 1 + d) ∈ sLiveBack n sgs o r
        · simp only [hmemL,↓reduceIte]
          set L1:=(sLiveBack n sgs o r).filter (· != n + (p + 1 + d))
          set L2:=if sgs[p + 1 + d].a ∈ L1 then L1 else sgs[p + 1 + d].a :: L1
          have hu1:u ∈ L1:=List.mem_filter.2 ⟨hu,by simp [huq]⟩
          have hu2:u ∈ L2:=by dsimp only [L2]; split_ifs <;> simp [hu1]
          by_cases hb:sgs[p + 1 + d].b ∈ L2 <;> simp [hb,hu2]
        · simp only [hmemL,↓reduceIte]; exact hu
  have ho_eq:∀ k < 1 <<< n,
      (sWiresFrom post (sWiresFrom pre (List.ofFn (pt n k)) ++ [false])).getD o false =
      (sWiresFrom sgs (List.ofFn (pt n k))).getD o false :=
    fun k hk => hagree k hk 0 (Nat.zero_le _) o List.mem_cons_self
  cases hsto:res.1.getD o (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨z1,o1,hz1,ho1,hne⟩:=hnc
    have h1:=((hinv_fake z1 hz1).2 o).2; rw [hsto,ho_eq z1 hz1] at h1
    have h2:=((hinv_fake o1 ho1).2 o).2; rw [hsto,ho_eq o1 ho1] at h2
    have e1:=hev z1 hz1; have e2:=hev o1 ho1
    simp only [sStatVal] at h1 h2
    rw [<- h1] at e1; rw [<- h2] at e2
    exact hne (e1.symm.trans e2)
  | inr pair =>
    obtain ⟨o',p'⟩:=pair
    obtain ⟨z1,_,hz1,_,_⟩:=hnc
    have ho':o' < n + res.2.length:=by
      have:=((hinv_fake z1 hz1).2 o).1; rwa [hsto] at this
    refine ⟨res.2,o',xor p' pol,hcl',hlen',ho',fun k hk _ => ?_⟩
    have h1:=((hinv_fake k hk).2 o).2; rw [hsto,ho_eq k hk] at h1
    simp only [sStatVal] at h1
    have e1:=hev k hk
    rw [<- e1,<- h1]
    cases ((sWiresFrom res.2 (List.ofFn (pt n k))).getD o' false) <;> cases p' <;> cases pol <;> rfl
theorem srun_of_hasSigned (n tgt cap:ℕ)
    (htgt_mask:tgt &&& maskN n = tgt)
    (htgt0:tgt.testBit 0 = false)
    (hnc:∃ z1 o1,z1 < 1 <<< n /\ o1 < 1 <<< n /\ tgt.testBit z1 ≠ tgt.testBit o1)
    (hall_ess:∀ i < n,∃ k1 k2,k1 < 1 <<< n /\ k2 < 1 <<< n /\
      (∀ j < n,j ≠ i -> k1.testBit j = k2.testBit j) /\ tgt.testBit k1 ≠ tgt.testBit k2)
    (h:HasSignedOn n (maskN n) tgt cap) :
    SRun (maskN n) tgt cap ((List.range n).map (inpW n)):=by
  classical
  have hex:∃ s,HasSignedOn n (maskN n) tgt s:=⟨cap,h⟩
  set sMin:=Nat.find hex
  have hsMin_le:sMin ≤ cap:=Nat.find_min' hex h
  have hsMin_ok:HasSignedOn n (maskN n) tgt sMin:=Nat.find_spec hex
  have hsMin_min:∀ s' < sMin,¬ HasSignedOn n (maskN n) tgt s':=fun s' hlt => Nat.find_min hex hlt
  obtain ⟨sgs,o,pol,hcl,hslen,ho,hev_mask⟩:=hsMin_ok
  have hev:∀ k < 1 <<< n,xor ((sWiresFrom sgs (List.ofFn (pt n k))).getD o false) pol = tgt.testBit k :=
    fun k hk => hev_mask k hk (by rw [testBit_maskN]; simp [hk])
  have hlen_eq:sgs.length = sMin:=by
    by_contra hne
    have hlt:sgs.length < sMin:=by omega
    exact hsMin_min sgs.length hlt ⟨sgs,o,pol,hcl,le_refl _,ho,hev_mask⟩
  have h0mask:(maskN n).testBit 0 = true:=by rw [testBit_maskN]; simp [Nat.shiftLeft_eq]
  let wireRaw (u:ℕ):ℕ:=encB n (fun k => (sWiresFrom sgs (List.ofFn (pt n k))).getD u false)
  let wireN (u:ℕ):ℕ:=normW (maskN n) (wireRaw u)
  have hraw_mask:∀ u,wireRaw u &&& maskN n = wireRaw u:=by
    intro u; apply Nat.eq_of_testBit_eq; intro k
    simp only [Nat.testBit_and,wireRaw,encB_testBit,testBit_maskN]
    cases decide (k < 1 <<< n) <;> simp
  have hinp_eq:∀ i < n,wireN i = inpW n i:=by
    intro i hi
    have hraw_i:wireRaw i = inpW n i:=by
      apply Nat.eq_of_testBit_eq; intro k
      simp only [wireRaw,inpW,encB_testBit]
      by_cases hk:k < 1 <<< n
      · simp only [hk,decide_true,Bool.true_and]
        rw [getD_sWiresFrom _ _ i (by simp [hi]),ofFn_pt_getD n k i hi]
      · simp [hk]
    rw [show wireN i = normW (maskN n) (wireRaw i) from rfl,hraw_i]
    apply normW_of_bit0_false
    simp only [inpW,encB_testBit,Nat.zero_testBit,Bool.and_false]
  have hgate_live:∀ p < sgs.length,n + p ∈ sLiveBack n sgs o (sgs.length - (p + 1)):=by
    intro p hp
    by_contra hdead
    have hshort:=sSubst_delete_dead n sgs p sgs[p] hcl (List.getElem?_eq_getElem hp) o pol ho tgt hev hdead hnc
    exact hsMin_min (sgs.length - 1) (by omega) hshort
  have hgate_nonconst:∀ p < sgs.length,wireN (n + p) ≠ 0 /\ wireN (n + p) ≠ maskN n:=by
    intro p hp
    have hnotc:∀ c:Bool,(∀ k < 1 <<< n,(sWiresFrom sgs (List.ofFn (pt n k))).getD (n + p) false = c) -> False:=by
      intro c hc
      have hshort:=sSubst_delete_gate n sgs p sgs[p] hcl (List.getElem?_eq_getElem hp) (Sum.inl c) trivial
        (fun k hk => by simp only [sStatVal]; exact (hc k hk).symm) o pol ho tgt hev hnc
      exact hsMin_min (sgs.length - 1) (by omega) hshort
    constructor
    · intro hz
      apply hnotc ((wireRaw (n + p)).testBit 0)
      intro k hk
      have hmk:(maskN n).testBit k = true:=by rw [testBit_maskN]; simp [hk]
      have hb:=congrArg (fun x => x.testBit k) hz
      rw [show wireN (n + p) = normW (maskN n) (wireRaw (n + p)) from rfl,
          testBit_normW (maskN n) _ k h0mask hmk] at hb
      simp only [Nat.zero_testBit] at hb
      have hrawk:(wireRaw (n + p)).testBit k = (sWiresFrom sgs (List.ofFn (pt n k))).getD (n + p) false:=by
        simp [wireRaw,encB_testBit,hk]
      rw [<- hrawk]
      cases h1:(wireRaw (n + p)).testBit k <;> cases h2:(wireRaw (n + p)).testBit 0 <;> simp [h1,h2] at hb ⊢
    · intro hm
      have hb0:=congrArg (fun x => x.testBit 0) hm
      rw [show wireN (n + p) = normW (maskN n) (wireRaw (n + p)) from rfl,normW_bit0 _ _ h0mask,h0mask] at hb0
      cases hb0
  have hgate_fresh:∀ p < sgs.length,∀ j < n + p,wireN (n + p) ≠ wireN j:=by
    intro p hp j hj heq
    let hpol:=xor ((wireRaw (n + p)).testBit 0) ((wireRaw j).testBit 0)
    have hval:∀ k < 1 <<< n,
        sStatVal (sWiresFrom (sgs.take p) (List.ofFn (pt n k))) (Sum.inr (j,hpol)) =
        (sWiresFrom sgs (List.ofFn (pt n k))).getD (n + p) false:=by
      intro k hk
      have hmk:(maskN n).testBit k = true:=by rw [testBit_maskN]; simp [hk]
      have hb:=congrArg (fun x => x.testBit k) heq
      rw [show wireN (n + p) = normW (maskN n) (wireRaw (n + p)) from rfl,
          show wireN j = normW (maskN n) (wireRaw j) from rfl,
          testBit_normW (maskN n) _ k h0mask hmk,testBit_normW (maskN n) _ k h0mask hmk] at hb
      have hrp:(wireRaw (n + p)).testBit k = (sWiresFrom sgs (List.ofFn (pt n k))).getD (n + p) false:=by
        simp [wireRaw,encB_testBit,hk]
      have hrj:(wireRaw j).testBit k = (sWiresFrom sgs (List.ofFn (pt n k))).getD j false:=by
        simp [wireRaw,encB_testBit,hk]
      have htake_j:(sWiresFrom (sgs.take p) (List.ofFn (pt n k))).getD j false =
          (sWiresFrom sgs (List.ofFn (pt n k))).getD j false:=by
        have hsp:sgs = sgs.take p ++ sgs.drop p:=(List.take_append_drop p sgs).symm
        conv_rhs => rw [hsp,sWiresFrom_append]
        rw [getD_sWiresFrom (sgs.drop p) _ j (by rw [length_sWiresFrom,List.length_ofFn,List.length_take]; omega)]
      simp only [sStatVal,htake_j]
      rw [hrp,hrj] at hb
      dsimp only [hpol]
      generalize (sWiresFrom sgs (List.ofFn (pt n k))).getD (n + p) false = v1 at hb ⊢
      generalize (sWiresFrom sgs (List.ofFn (pt n k))).getD j false = v2 at hb ⊢
      generalize (wireRaw (n + p)).testBit 0 = b1 at hb ⊢
      generalize (wireRaw j).testBit 0 = b2 at hb ⊢
      cases v1 <;> cases v2 <;> cases b1 <;> cases b2 <;> simp at hb ⊢
    have hshort:=sSubst_delete_gate n sgs p sgs[p] hcl (List.getElem?_eq_getElem hp)
      (Sum.inr (j,hpol)) hj hval o pol ho tgt hev hnc
    exact hsMin_min (sgs.length - 1) (by omega) hshort
  have hinp_inj:∀ i j,i < n -> j < n -> wireN i = wireN j -> i = j:=by
    intro i j hi hj heq
    rw [hinp_eq i hi,hinp_eq j hj] at heq
    by_contra hne
    have hlt:1 <<< i < 1 <<< n:=by
      simp only [Nat.shiftLeft_eq,Nat.one_mul]; exact Nat.pow_lt_pow_right (by omega) hi
    have hb:=congrArg (fun x => x.testBit (1 <<< i)) heq
    rw [inpW_testBit n i (1 <<< i) hlt,inpW_testBit n j (1 <<< i) hlt] at hb
    simp [testBit_one_shiftLeft,Ne.symm hne] at hb
  have hwireN_inj:∀ u v,u < n + sgs.length -> v < n + sgs.length -> wireN u = wireN v -> u = v:=by
    intro u v hu hv heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · by_cases hvn:v < n
      · exact hne (hinp_inj u v (by omega) hvn heq)
      · exact hgate_fresh (v - n) (by omega) u (by omega) (by rw [show n + (v - n) = v by omega]; exact heq.symm)
    · by_cases hun:u < n
      · exact hne (hinp_inj u v hun (by omega) heq)
      · exact hgate_fresh (u - n) (by omega) v (by omega) (by rw [show n + (u - n) = u by omega]; exact heq)
  have ho_tgt:wireN o = tgt:=by
    apply Nat.eq_of_testBit_eq; intro k
    by_cases hk:k < 1 <<< n
    · have hmk:(maskN n).testBit k = true:=by rw [testBit_maskN]; simp [hk]
      rw [show wireN o = normW (maskN n) (wireRaw o) from rfl,testBit_normW (maskN n) _ k h0mask hmk]
      have h0lt:0 < 1 <<< n:=by rw [Nat.shiftLeft_eq,Nat.one_mul]; exact Nat.two_pow_pos n
      have hrk:(wireRaw o).testBit k = (sWiresFrom sgs (List.ofFn (pt n k))).getD o false:=by
        simp only [wireRaw,encB_testBit,hk,decide_true,Bool.true_and]
      have hr0:(wireRaw o).testBit 0 = (sWiresFrom sgs (List.ofFn (pt n 0))).getD o false:=by
        simp only [wireRaw,encB_testBit,h0lt,decide_true,Bool.true_and]
      rw [hrk,hr0]
      have ek:=hev k hk
      have e0:=hev 0 h0lt; rw [htgt0] at e0
      generalize (sWiresFrom sgs (List.ofFn (pt n k))).getD o false = vk at ek ⊢
      generalize (sWiresFrom sgs (List.ofFn (pt n 0))).getD o false = v0 at e0 ⊢
      cases vk <;> cases v0 <;> cases pol <;> cases ht:tgt.testBit k <;> simp [ht] at ek e0 ⊢
    · have hmk:(maskN n).testBit k = false:=by rw [testBit_maskN]; simp [hk]
      have htk:tgt.testBit k = false:=by
        have:=congrArg (fun x => x.testBit k) htgt_mask; simp [Nat.testBit_and,hmk] at this; exact this
      rw [htk]
      have hwk:(wireRaw o).testBit k = false:=by simp [wireRaw,encB_testBit,hk]
      unfold wireN normW
      cases (wireRaw o).testBit 0 <;> simp [Nat.testBit_xor,hwk,hmk]
  have hrun_back:∀ r ≤ sgs.length,
      SRun (maskN n) tgt (cap - sgs.length + r) ((sLiveBack n sgs o r).map wireN):=by
    intro r
    induction r with
    | zero =>
      intro _
      simp only [sLiveBack,List.map_cons,List.map_nil,ho_tgt,Nat.add_zero]
      exact SRun.done _
    | succ r ih =>
      intro hr
      set p:=sgs.length - 1 - r
      have hplt:p < sgs.length:=by omega
      have hget:sgs[p]? = some sgs[p]:=List.getElem?_eq_getElem hplt
      set g:=sgs[p]
      obtain ⟨hga,hgb,_⟩:=hcl p g hget
      set Lprev:=sLiveBack n sgs o r
      set Lcur:=sLiveBack n sgs o (r + 1)
      have hLcur_eq:Lcur = sLiveStep n p g Lprev:=by
        simp [Lcur,sLiveBack,p,hget,Lprev]
      have hnp_in:n + p ∈ Lprev:=by
        have:=hgate_live p hplt
        have hidx:sgs.length - (p + 1) = r:=by omega
        rwa [hidx] at this
      have hLcur_lt:∀ u ∈ Lcur,u < n + p:=by
        intro u hu
        have:=sLiveBack_lt n sgs hcl o ho (r + 1) hr u hu
        omega
      have hLprev_lt:∀ u ∈ Lprev,u < n + (p + 1):=by
        intro u hu
        have:=sLiveBack_lt n sgs hcl o ho r (by omega) u hu
        omega
      have hga_in:g.a ∈ Lcur:=by
        rw [hLcur_eq]; unfold sLiveStep; simp only [hnp_in,↓reduceIte]
        set L1:=Lprev.filter (· != n + p)
        set L2:=if g.a ∈ L1 then L1 else g.a :: L1
        have hm2:g.a ∈ L2:=by dsimp only [L2]; split_ifs with h <;> simp [h]
        by_cases hb:g.b ∈ L2 <;> simp [hb,hm2]
      have hgb_in:g.b ∈ Lcur:=by
        rw [hLcur_eq]; unfold sLiveStep; simp only [hnp_in,↓reduceIte]
        set L1:=Lprev.filter (· != n + p)
        set L2:=if g.a ∈ L1 then L1 else g.a :: L1
        by_cases hb:g.b ∈ L2 <;> simp [hb]
      have hraw_p:wireRaw (n + p) = encB n (fun k => sOpEval g.op ((wireRaw g.a).testBit k) ((wireRaw g.b).testBit k)):=by
        apply Nat.eq_of_testBit_eq; intro k
        simp only [wireRaw,encB_testBit]
        by_cases hk:k < 1 <<< n
        · simp only [hk,decide_true,Bool.true_and]
          exact sWiresFrom_getD_gate n sgs p g hget hga hgb (List.ofFn (pt n k)) (by simp)
        · simp [hk]
      obtain ⟨op',hop',hzp⟩:=normW_sOpEval n g.op (wireRaw g.a) (wireRaw g.b) (hraw_mask g.a) (hraw_mask g.b)
      have hzp':wireN (n + p) = applyOp (maskN n) op' (wireN g.a) (wireN g.b):=by
        rw [show wireN (n + p) = normW (maskN n) (wireRaw (n + p)) from rfl,hraw_p]
        exact hzp
      have hwa_ne_wb:wireN g.a ≠ wireN g.b:=by
        intro heq
        have hga_eq_gb:g.a = g.b:=hwireN_inj g.a g.b (by omega) (by omega) heq
        rw [heq] at hzp'
        have hnb0:(wireN g.b).testBit 0 = false:=normW_bit0 _ _ h0mask
        have hnbm:wireN g.b &&& maskN n = wireN g.b:=normW_le_mask n _ (hraw_mask g.b)
        have hcontr:wireN (n + p) = 0 \/ wireN (n + p) = wireN g.b:=by
          rw [hzp']
          rcases op' with _ | _ | _ | op'
          · right; simp [applyOp,Nat.and_self,normW_of_bit0_false _ _ hnb0]
          · right; simp [applyOp,Nat.or_self,normW_of_bit0_false _ _ hnb0]
          · left
            have h0:wireN g.b &&& (wireN g.b ^^^ maskN n) = 0:=by
              apply Nat.eq_of_testBit_eq; intro k
              simp only [Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit]
              cases h1:(wireN g.b).testBit k <;> cases h2:(maskN n).testBit k <;> simp
              exfalso
              have:=congrArg (fun x => x.testBit k) hnbm
              simp [Nat.testBit_and,h1,h2] at this
            simp [applyOp,h0,normW]
          · left
            have h0:(wireN g.b ^^^ maskN n) &&& wireN g.b = 0:=by
              apply Nat.eq_of_testBit_eq; intro k
              simp only [Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit]
              cases h1:(wireN g.b).testBit k <;> cases h2:(maskN n).testBit k <;> simp
              exfalso
              have:=congrArg (fun x => x.testBit k) hnbm
              simp [Nat.testBit_and,h1,h2] at this
            simp [applyOp,h0,normW]
        rcases hcontr with hz | halias
        · exact (hgate_nonconst p hplt).1 hz
        · exact hgate_fresh p hplt g.b hgb halias
      have hnd_cur:(Lcur.map wireN).Nodup:=by
        apply List.Nodup.map_on _ (sLiveBack_nodup n sgs o (r + 1))
        intro u hu v hv heq
        exact hwireN_inj u v (by have:=hLcur_lt u hu; omega) (by have:=hLcur_lt v hv; omega) heq
      have hnd_prev:(Lprev.map wireN).Nodup:=by
        apply List.Nodup.map_on _ (sLiveBack_nodup n sgs o r)
        intro u hu v hv heq
        exact hwireN_inj u v (by have:=hLprev_lt u hu; omega) (by have:=hLprev_lt v hv; omega) heq
      have hnz_cur:wireN (n + p) ∉ Lcur.map wireN:=by
        intro hmem
        obtain ⟨u,hu,heq⟩:=List.mem_map.1 hmem
        exact hgate_fresh p hplt u (hLcur_lt u hu) heq.symm
      set kc:ℕ :=
        match decide (g.a ∈ Lprev),decide (g.b ∈ Lprev) with
        | false,false => 0
        | true, false => 1
        | false,true  => 2
        | true, true  => 3
      have hkc_lt:kc < 4:=by
        dsimp only [kc]; cases decide (g.a ∈ Lprev) <;> cases decide (g.b ∈ Lprev) <;> decide
      have hperm:(Lprev.map wireN).Perm (mkCand (Lcur.map wireN) (wireN g.a) (wireN g.b) (wireN (n + p)) kc):=by
        apply (List.perm_ext_iff_of_nodup hnd_prev (mkCand_nodup hnd_cur (List.mem_map_of_mem hga_in)
          (List.mem_map_of_mem hgb_in) hwa_ne_wb hnz_cur)).2
        intro w
        constructor
        · intro hw
          obtain ⟨u,hu,rfl⟩:=List.mem_map.1 hw
          by_cases hup:u = n + p
          · subst hup
            rcases hkc_cases:kc with _ | _ | _ | kc' <;> simp [mkCand]
          · by_cases hua:u = g.a
            · subst hua
              have ha_in:g.a ∈ Lprev:=hu
              simp only [kc,ha_in,decide_true]
              cases decide (g.b ∈ Lprev) <;> simp [mkCand]
            · by_cases hub:u = g.b
              · subst hub
                have hb_in:g.b ∈ Lprev:=hu
                simp only [kc,hb_in,decide_true]
                cases decide (g.a ∈ Lprev) <;> simp [mkCand]
              · have hu_cur:u ∈ Lcur:=by
                  rw [hLcur_eq]; unfold sLiveStep; simp only [hnp_in,↓reduceIte]
                  set L1:=Lprev.filter (· != n + p)
                  set L2:=if g.a ∈ L1 then L1 else g.a :: L1
                  have hu1:u ∈ L1:=List.mem_filter.2 ⟨hu,by simp [hup]⟩
                  have hu2:u ∈ L2:=by dsimp only [L2]; split_ifs <;> simp [hu1]
                  by_cases hb:g.b ∈ L2 <;> simp [hb,hu2]
                have hne_a:wireN u ≠ wireN g.a:=fun h => hua (hwireN_inj u g.a (by have:=hLprev_lt u hu; omega) (by omega) h)
                have hne_b:wireN u ≠ wireN g.b:=fun h => hub (hwireN_inj u g.b (by have:=hLprev_lt u hu; omega) (by omega) h)
                have hmem_er:wireN u ∈ ((Lcur.map wireN).erase (wireN g.a)).erase (wireN g.b) :=
                  (List.mem_erase_of_ne hne_b).2 ((List.mem_erase_of_ne hne_a).2 (List.mem_map_of_mem hu_cur))
                rcases hkc_cases:kc with _ | _ | _ | kc' <;> simp [mkCand,hmem_er]
        · intro hw
          have hmem_case:w = wireN (n + p) \/ (w = wireN g.a /\ g.a ∈ Lprev) \/ (w = wireN g.b /\ g.b ∈ Lprev) \/
              (w ∈ Lcur.map wireN /\ w ≠ wireN g.a /\ w ≠ wireN g.b):=by
            dsimp only [kc] at hw
            cases ha:decide (g.a ∈ Lprev) <;> cases hb:decide (g.b ∈ Lprev) <;>
              simp only [ha,hb,mkCand,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
            · rcases hw with h | rfl
              · have hne_b:w ≠ wireN g.b:=fun heq => by
                  subst heq; exact ((hnd_cur.erase _).not_mem_erase) h
                have h1:=List.mem_of_mem_erase h
                have hne_a:w ≠ wireN g.a:=fun heq => by
                  subst heq; exact (hnd_cur.not_mem_erase) h1
                exact Or.inr (Or.inr (Or.inr ⟨List.mem_of_mem_erase h1,hne_a,hne_b⟩))
              · exact Or.inl rfl
            · rcases hw with (h | rfl) | rfl
              · have hne_b:w ≠ wireN g.b:=fun heq => by
                  subst heq; exact ((hnd_cur.erase _).not_mem_erase) h
                have h1:=List.mem_of_mem_erase h
                have hne_a:w ≠ wireN g.a:=fun heq => by
                  subst heq; exact (hnd_cur.not_mem_erase) h1
                exact Or.inr (Or.inr (Or.inr ⟨List.mem_of_mem_erase h1,hne_a,hne_b⟩))
              · exact Or.inl rfl
              · exact Or.inr (Or.inr (Or.inl ⟨rfl,of_decide_eq_true hb⟩))
            · rcases hw with (h | rfl) | rfl
              · have hne_b:w ≠ wireN g.b:=fun heq => by
                  subst heq; exact ((hnd_cur.erase _).not_mem_erase) h
                have h1:=List.mem_of_mem_erase h
                have hne_a:w ≠ wireN g.a:=fun heq => by
                  subst heq; exact (hnd_cur.not_mem_erase) h1
                exact Or.inr (Or.inr (Or.inr ⟨List.mem_of_mem_erase h1,hne_a,hne_b⟩))
              · exact Or.inl rfl
              · exact Or.inr (Or.inl ⟨rfl,of_decide_eq_true ha⟩)
            · rcases hw with (h | rfl) | (rfl | rfl)
              · have hne_b:w ≠ wireN g.b:=fun heq => by
                  subst heq; exact ((hnd_cur.erase _).not_mem_erase) h
                have h1:=List.mem_of_mem_erase h
                have hne_a:w ≠ wireN g.a:=fun heq => by
                  subst heq; exact (hnd_cur.not_mem_erase) h1
                exact Or.inr (Or.inr (Or.inr ⟨List.mem_of_mem_erase h1,hne_a,hne_b⟩))
              · exact Or.inl rfl
              · exact Or.inr (Or.inl ⟨rfl,of_decide_eq_true ha⟩)
              · exact Or.inr (Or.inr (Or.inl ⟨rfl,of_decide_eq_true hb⟩))
          rcases hmem_case with rfl | ⟨rfl,ha⟩ | ⟨rfl,hb⟩ | ⟨hwcur,hnea,hneb⟩
          · exact List.mem_map_of_mem hnp_in
          · exact List.mem_map_of_mem ha
          · exact List.mem_map_of_mem hb
          · obtain ⟨u,hu,rfl⟩:=List.mem_map.1 hwcur
            rw [hLcur_eq] at hu; unfold sLiveStep at hu; simp only [hnp_in,↓reduceIte] at hu
            set L1:=Lprev.filter (· != n + p)
            set L2:=if g.a ∈ L1 then L1 else g.a :: L1
            have hu_L2:u ∈ L2:=by
              by_cases hb:g.b ∈ L2
              · simp only [hb,↓reduceIte] at hu; exact hu
              · simp only [hb,↓reduceIte,List.mem_cons] at hu
                rcases hu with rfl | hu'
                · exact absurd rfl hneb
                · exact hu'
            have hu_L1:u ∈ L1:=by
              dsimp only [L2] at hu_L2
              by_cases ha:g.a ∈ L1
              · simp only [ha,↓reduceIte] at hu_L2; exact hu_L2
              · simp only [ha,↓reduceIte,List.mem_cons] at hu_L2
                rcases hu_L2 with rfl | hu'
                · exact absurd rfl hnea
                · exact hu'
            exact List.mem_map_of_mem (List.mem_filter.1 hu_L1).1
      have hcw_len:(mkCand (Lcur.map wireN) (wireN g.a) (wireN g.b) (wireN (n + p)) kc).length ≤ (cap - sgs.length + r) + 1:=by
        rw [<- hperm.length_eq,List.length_map]
        have hlen_p:Lprev.length ≤ r + 1:=sLiveBack_length n sgs o r
        omega
      have hstep:=SRun.step (cap - sgs.length + r) (Lcur.map wireN) (wireN g.a) (wireN g.b) op' kc
        hnd_cur (List.mem_map_of_mem hga_in) (List.mem_map_of_mem hgb_in) hwa_ne_wb hop' hkc_lt
        (by rw [<- hzp']; exact (hgate_nonconst p hplt).1)
        (by rw [<- hzp']; exact (hgate_nonconst p hplt).2)
        (by rw [<- hzp']; exact hnz_cur)
        (by rw [<- hzp']; exact hcw_len)
        (by rw [<- hzp']; exact SRun.perm hperm (ih (by omega)))
      have heq_s:cap - sgs.length + (r + 1) = (cap - sgs.length + r) + 1:=by omega
      rw [heq_s]
      exact hstep
  have hrun0:=hrun_back sgs.length (le_refl _)
  have hcap_eq:cap - sgs.length + sgs.length = cap:=by omega
  rw [hcap_eq] at hrun0
  have hall_in:∀ i < n,i ∈ sLiveBack n sgs o sgs.length:=by
    intro i hi
    have hback_eq:∀ (w1 w2:List Bool),w1.length = n -> w2.length = n ->
        (∀ u ∈ sLiveBack n sgs o sgs.length,(sWiresFrom sgs w1).getD u false = (sWiresFrom sgs w2).getD u false) ->
        ∀ r ≤ sgs.length,∀ u ∈ sLiveBack n sgs o r,
          (sWiresFrom sgs w1).getD u false = (sWiresFrom sgs w2).getD u false:=by
      intro w1 w2 hw1 hw2 h0
      suffices key:∀ d ≤ sgs.length,∀ u ∈ sLiveBack n sgs o (sgs.length - d),
          (sWiresFrom sgs w1).getD u false = (sWiresFrom sgs w2).getD u false by
        intro r hr; rw [<- show sgs.length - (sgs.length - r) = r by omega]; exact key (sgs.length - r) (by omega)
      intro d
      induction d with
      | zero => intro _ u hu; simpa using h0 u hu
      | succ d ih =>
        intro hd u hu
        set r:=sgs.length - (d + 1)
        have hr1:sgs.length - d = r + 1:=by omega
        have hq:sgs.length - 1 - r = d:=by omega
        have hget:sgs[d]? = some sgs[d]:=List.getElem?_eq_getElem (by omega)
        have hprev:=ih (by omega); rw [hr1] at hprev; simp only [sLiveBack,hq,hget] at hprev
        obtain ⟨hga,hgb,_⟩:=hcl d sgs[d] hget
        by_cases hud:u = n + d
        · subst hud
          have hmemL:n + d ∈ sLiveBack n sgs o r:=hu
          set L':=sLiveStep n d sgs[d] (sLiveBack n sgs o r)
          have hga_m:sgs[d].a ∈ L':=by
            unfold L' sLiveStep; simp only [hmemL,↓reduceIte]
            set L1:=(sLiveBack n sgs o r).filter (· != n + d)
            set L2:=if sgs[d].a ∈ L1 then L1 else sgs[d].a :: L1
            have hm2:sgs[d].a ∈ L2:=by dsimp only [L2]; split_ifs with h <;> simp [h]
            by_cases hb:sgs[d].b ∈ L2 <;> simp [hb,hm2]
          have hgb_m:sgs[d].b ∈ L':=by
            unfold L' sLiveStep; simp only [hmemL,↓reduceIte]
            set L1:=(sLiveBack n sgs o r).filter (· != n + d)
            set L2:=if sgs[d].a ∈ L1 then L1 else sgs[d].a :: L1
            by_cases hb:sgs[d].b ∈ L2 <;> simp [hb]
          rw [sWiresFrom_getD_gate n sgs d sgs[d] hget hga hgb w1 hw1,
              sWiresFrom_getD_gate n sgs d sgs[d] hget hga hgb w2 hw2,
              hprev _ hga_m,hprev _ hgb_m]
        · apply hprev u
          unfold sLiveStep
          by_cases hmemL:n + d ∈ sLiveBack n sgs o r
          · simp only [hmemL,↓reduceIte]
            set L1:=(sLiveBack n sgs o r).filter (· != n + d)
            set L2:=if sgs[d].a ∈ L1 then L1 else sgs[d].a :: L1
            have hu1:u ∈ L1:=List.mem_filter.2 ⟨hu,by simp [hud]⟩
            have hu2:u ∈ L2:=by dsimp only [L2]; split_ifs <;> simp [hu1]
            by_cases hb:sgs[d].b ∈ L2 <;> simp [hb,hu2]
          · simp only [hmemL,↓reduceIte]; exact hu
    by_contra hnot
    obtain ⟨k1,k2,hk1,hk2,hagree,hne⟩:=hall_ess i hi
    have ho_eq:=hback_eq (List.ofFn (pt n k1)) (List.ofFn (pt n k2)) (by simp) (by simp)
      (by
        intro u hu
        have hun:u < n:=by
          have:=sLiveBack_lt n sgs hcl o ho sgs.length (le_refl _) u hu; omega
        have hui:u ≠ i:=fun h => hnot (h ▸ hu)
        rw [getD_sWiresFrom _ _ u (by simp [hun]),getD_sWiresFrom _ _ u (by simp [hun]),
            ofFn_pt_getD n k1 u hun,ofFn_pt_getD n k2 u hun]
        exact hagree u hun hui)
      0 (Nat.zero_le _) o List.mem_cons_self
    have e1:=hev k1 hk1; have e2:=hev k2 hk2
    rw [ho_eq] at e1
    exact hne (e1.symm.trans e2)
  have hperm0:(sLiveBack n sgs o sgs.length).Perm (List.range n):=by
    apply (List.perm_ext_iff_of_nodup (sLiveBack_nodup n sgs o sgs.length) List.nodup_range).2
    intro u
    rw [List.mem_range]
    exact ⟨fun hu => by have:=sLiveBack_lt n sgs hcl o ho sgs.length (le_refl _) u hu; omega,
           fun hu => hall_in u hu⟩
  have hmap_eq:(List.range n).map wireN = (List.range n).map (inpW n):=by
    apply List.map_congr_left
    intro i hi; exact hinp_eq i (List.mem_range.1 hi)
  exact SRun.perm (hmap_eq ▸ hperm0.map wireN) hrun0
def isUnsepOne (full z:ℕ):List ℕ -> ℕ -> Bool
  | _,0 => false
  | [],_ => true
  | w :: ws,m => isUnsepOne full z ws (if w.testBit z then m &&& w else m &&& (w ^^^ full))
theorem isUnsepOne_eq_foldl (full z:ℕ) (ws:List ℕ) :
    ∀ m:ℕ,isUnsepOne full z ws m =
      ((ws.foldl (fun acc w => if w.testBit z then acc &&& w else acc &&& (w ^^^ full)) m) != 0):=by
  induction ws with
  | nil => intro m; cases m <;> rfl
  | cons w ws ih =>
    intro m
    cases m with
    | zero =>
      simp only [isUnsepOne,List.foldl_cons]
      have h0:(if w.testBit z then 0 &&& w else 0 &&& (w ^^^ full)) = 0:=by split_ifs <;> simp
      rw [h0,<- ih 0]
      cases ws <;> rfl
    | succ m =>
      simp only [isUnsepOne,List.foldl_cons]
      exact ih _
def isUnsep (full tgt:ℕ) (zs ws:List ℕ):Bool :=
  zs.any fun z => isUnsepOne full z ws tgt
theorem foldl_unsep_testBit (full z:ℕ) (ws:List ℕ) (o:ℕ) (hfo:full.testBit o = true) :
    ∀ m:ℕ,
      (ws.foldl (fun acc w => if w.testBit z then acc &&& w else acc &&& (w ^^^ full)) m).testBit o = true ->
      m.testBit o = true /\ ∀ w ∈ ws,w.testBit o = w.testBit z:=by
  induction ws with
  | nil => intro m hm; exact ⟨hm,fun _ h => by cases h⟩
  | cons w ws ih =>
    intro m hm
    obtain ⟨hstep,hrest⟩:=ih _ hm
    cases hwz:w.testBit z with
    | true =>
      simp only [hwz,↓reduceIte,Nat.testBit_and,Bool.and_eq_true] at hstep
      refine ⟨hstep.1,fun u hu => ?_⟩
      rcases List.mem_cons.1 hu with rfl | hu'
      · rw [hstep.2,hwz]
      · exact hrest u hu'
    | false =>
      simp only [hwz,Bool.false_eq_true,↓reduceIte,Nat.testBit_and,Nat.testBit_xor,hfo,
        Bool.and_eq_true,Bool.bne_true,Bool.not_eq_true'] at hstep
      refine ⟨hstep.1,fun u hu => ?_⟩
      rcases List.mem_cons.1 hu with rfl | hu'
      · rw [hstep.2,hwz]
      · exact hrest u hu'
theorem srun_preserves_agree (full tgt z o:ℕ) (h0:full.testBit 0 = true)
    (hfz:full.testBit z = true) (hfo:full.testBit o = true) :
    ∀ s ws,SRun full tgt s ws -> (∀ w ∈ ws,w.testBit o = w.testBit z) ->
      tgt.testBit o = tgt.testBit z:=by
  intro s ws hrun
  induction hrun with
  | done _ => intro hag; exact hag tgt List.mem_cons_self
  | perm hperm _ ih => intro hag; exact ih (fun w hw => hag w (hperm.subset hw))
  | step s ws a b op kc _ ha hb _ _ _ _ _ _ _ _ ih =>
    intro hag
    apply ih
    intro w hw
    rcases mkCand_subset ha hb w hw with rfl | hw'
    · have hza:a.testBit o = a.testBit z:=hag a ha
      have hzb:b.testBit o = b.testBit z:=hag b hb
      rcases op with _ | _ | _ | op <;>
        simp [applyOp,testBit_normW full _ o h0 hfo,testBit_normW full _ z h0 hfz,
          Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,hfo,hfz,hza,hzb]
    · exact hag w hw'
theorem isUnsep_sound (n tgt:ℕ) (zs:List ℕ)
    (htgt_mask:tgt &&& maskN n = tgt)
    (hzs:∀ z ∈ zs,z < 1 <<< n /\ tgt.testBit z = false)
    (s:ℕ) (ws:List ℕ) (hu:isUnsep (maskN n) tgt zs ws = true) :
    ¬ SRun (maskN n) tgt s ws:=by
  intro hrun
  simp only [isUnsep,isUnsepOne_eq_foldl,List.any_eq_true,bne_iff_ne,ne_eq] at hu
  obtain ⟨z,hz_mem,hne0⟩:=hu
  obtain ⟨hzlt,htz⟩:=hzs z hz_mem
  set res:=ws.foldl (fun m w => if w.testBit z then m &&& w else m &&& (w ^^^ maskN n)) tgt
  have hres_le:res &&& maskN n = res:=by
    have hfold:∀ (L:List ℕ) (m:ℕ),m &&& maskN n = m ->
        (L.foldl (fun acc w => if w.testBit z then acc &&& w else acc &&& (w ^^^ maskN n)) m) &&& maskN n =
        L.foldl (fun acc w => if w.testBit z then acc &&& w else acc &&& (w ^^^ maskN n)) m:=by
      intro L
      induction L with
      | nil => intro m hm; exact hm
      | cons w L ih =>
        intro m hm
        apply ih
        apply Nat.eq_of_testBit_eq; intro k
        have hmk:=congrArg (fun x => x.testBit k) hm
        simp only [Nat.testBit_and] at hmk ⊢
        split_ifs <;> simp only [Nat.testBit_and]
        · cases hmk':(maskN n).testBit k <;> simp [hmk'] at hmk ⊢; simp [hmk]
        · cases hmk':(maskN n).testBit k <;> simp [hmk'] at hmk ⊢; simp [hmk]
    exact hfold ws tgt htgt_mask
  have hex_o:∃ o,res.testBit o = true:=by
    by_contra hno; push Not at hno
    apply hne0
    apply Nat.eq_of_testBit_eq; intro k
    simpa using Bool.eq_false_iff.2 (hno k)
  obtain ⟨o,ho⟩:=hex_o
  have hfo:(maskN n).testBit o = true:=by
    have:=congrArg (fun x => x.testBit o) hres_le
    simp [Nat.testBit_and,ho] at this; exact this
  have h0:(maskN n).testBit 0 = true:=by rw [testBit_maskN]; simp [Nat.shiftLeft_eq]
  have hfz:(maskN n).testBit z = true:=by rw [testBit_maskN]; simp [hzlt]
  obtain ⟨hto,hag⟩:=foldl_unsep_testBit (maskN n) z ws o hfo tgt ho
  have heq:=srun_preserves_agree (maskN n) tgt z o h0 hfz hfo s ws hrun hag
  rw [hto,htz] at heq
  cases heq
def RepOn (n rm:ℕ) (sgs:List SGate) (w:ℕ):Prop :=
  (w &&& rm = 0 \/ w &&& rm = rm) \/
  ∃ j < n + sgs.length,∃ pol:Bool,∀ k < 1 <<< n,rm.testBit k = true ->
    xor ((sWiresFrom sgs (List.ofFn (pt n k))).getD j false) pol = w.testBit k
def Available (n rm:ℕ) (ws:List ℕ) (k:ℕ):Prop :=
  ∃ sgs:List SGate,SCleanL n sgs /\ sgs.length ≤ k /\ ∀ w ∈ ws,RepOn n rm sgs w
theorem available_mono {n rm k k':ℕ} {ws:List ℕ} (hle:k ≤ k') (h:Available n rm ws k) :
    Available n rm ws k':=by
  obtain ⟨sgs,hcl,hlen,hrep⟩:=h
  exact ⟨sgs,hcl,Nat.le_trans hlen hle,hrep⟩
theorem available_perm {n rm k:ℕ} {ws ws':List ℕ} (hp:ws.Perm ws') (h:Available n rm ws k) :
    Available n rm ws' k:=by
  obtain ⟨sgs,hcl,hlen,hrep⟩:=h
  exact ⟨sgs,hcl,hlen,fun w hw => hrep w (hp.symm.subset hw)⟩
theorem available_inputs (n rm:ℕ):Available n rm ((List.range n).map (inpW n)) 0:=by
  refine ⟨[],fun _ _ h => by simp at h,le_refl _,fun w hw => ?_⟩
  obtain ⟨i,hi,rfl⟩:=List.mem_map.1 hw
  rw [List.mem_range] at hi
  refine Or.inr ⟨i,by simp [hi],false,fun k hk _ => ?_⟩
  simp only [sWiresFrom,List.foldl_nil,Bool.xor_false,ofFn_pt_getD n k i hi,inpW_testBit n i k hk]
theorem projSl_eq_zero_iff (sl:SliceData) (hlow:sl.rm &&& sl.low ≠ 0) (w:ℕ) :
    projSl sl w = 0 ↔ (w &&& sl.rm = 0 \/ w &&& sl.rm = sl.rm):=by
  unfold projSl
  set p:=w &&& sl.rm
  by_cases hpr:p = sl.rm
  · simp [hpr]
  · simp only [beq_iff_eq,hpr,↓reduceIte]
    by_cases hp0:p = 0
    · simp [hp0]
    · simp only [hp0,hpr,or_self,iff_false]
      by_cases hpl:(p &&& sl.low) ≠ 0
      · have hcond:(p != 0 && (p &&& sl.low) != 0) = true:=by simp [hp0,hpl]
        simp only [hcond,↓reduceIte]
        intro hxor
        apply hpr
        apply Nat.eq_of_testBit_eq; intro k
        have hxk:=congrArg (fun x => x.testBit k) hxor
        simp only [Nat.testBit_xor,Nat.zero_testBit] at hxk
        cases hp1:p.testBit k <;> cases hr1:sl.rm.testBit k <;> simp [hp1,hr1] at hxk ⊢
      · have hpl':p &&& sl.low = 0:=Classical.not_not.1 hpl
        have hcond:(p != 0 && (p &&& sl.low) != 0) = false:=by
          simp [hpl']
        rw [hcond]; simp only [Bool.false_eq_true,↓reduceIte]
        exact hp0
theorem projSl_eq_iff (n:ℕ) (sl:SliceData) (hrm:sl.rm &&& maskN n = sl.rm) (w u:ℕ)
    (heq:projSl sl w = projSl sl u) (hne0:projSl sl w ≠ 0) :
    (∀ k < 1 <<< n,sl.rm.testBit k = true -> w.testBit k = u.testBit k) \/
    (∀ k < 1 <<< n,sl.rm.testBit k = true -> w.testBit k = !u.testBit k):=by
  have hchar:∀ x,projSl sl x ≠ 0 -> projSl sl x = x &&& sl.rm \/ projSl sl x = (x &&& sl.rm) ^^^ sl.rm:=by
    intro x hx
    unfold projSl at hx ⊢
    dsimp only at hx ⊢
    split_ifs at hx ⊢
    · exact absurd rfl hx
    · exact Or.inr rfl
    · exact Or.inl rfl
  have h1:=hchar w hne0
  have h2:=hchar u (heq ▸ hne0)
  rw [heq] at h1
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · left; intro k _ hrmk
    have:=congrArg (fun x => x.testBit k) (h1.symm.trans h2)
    simp [Nat.testBit_and,hrmk] at this; exact this
  · right; intro k _ hrmk
    have:=congrArg (fun x => x.testBit k) (h1.symm.trans h2)
    simp only [Nat.testBit_and,Nat.testBit_xor,hrmk,Bool.and_true,Bool.bne_true] at this
    exact this
  · right; intro k _ hrmk
    have:=congrArg (fun x => x.testBit k) (h1.symm.trans h2)
    simp only [Nat.testBit_and,Nat.testBit_xor,hrmk,Bool.and_true,Bool.bne_true] at this
    cases hw1:w.testBit k <;> cases hu1:u.testBit k <;> simp [hw1,hu1] at this ⊢
  · left; intro k _ hrmk
    have:=congrArg (fun x => x.testBit k) (h1.symm.trans h2)
    simp only [Nat.testBit_and,Nat.testBit_xor,hrmk,Bool.and_true,Bool.bne_true] at this
    cases hw1:w.testBit k <;> cases hu1:u.testBit k <;> simp [hw1,hu1] at this ⊢
theorem repOn_applyOp_same (n rm op a b:ℕ) (sgs:List SGate)
    (hrm:rm &&& maskN n = rm)
    (ha:RepOn n rm sgs a) (hb:RepOn n rm sgs b)
    (hc:(a &&& rm = 0 \/ a &&& rm = rm) \/ (b &&& rm = 0 \/ b &&& rm = rm)) :
    RepOn n rm sgs (applyOp (maskN n) op a b):=by
  have h0:(maskN n).testBit 0 = true:=by rw [testBit_maskN]; simp [Nat.shiftLeft_eq]
  have hmk:∀ k,rm.testBit k = true -> (maskN n).testBit k = true:=by
    intro k hk; have:=congrArg (fun x => x.testBit k) hrm; simp [Nat.testBit_and,hk] at this; exact this
  have hconst_rep:∀ w:ℕ,(∀ k,rm.testBit k = true -> w.testBit k = false) \/
      (∀ k,rm.testBit k = true -> w.testBit k = true) -> RepOn n rm sgs w:=by
    intro w h
    left
    rcases h with h0' | h1'
    · left; apply Nat.eq_of_testBit_eq; intro k
      simp only [Nat.testBit_and,Nat.zero_testBit]
      cases hrmk:rm.testBit k with
      | false => simp
      | true => simp [h0' k hrmk]
    · right; apply Nat.eq_of_testBit_eq; intro k
      simp only [Nat.testBit_and]
      cases hrmk:rm.testBit k with
      | false => simp
      | true => simp [h1' k hrmk]
  have hrel_rep:∀ w u:ℕ,RepOn n rm sgs u ->
      ((∀ k,rm.testBit k = true -> w.testBit k = u.testBit k) \/
       (∀ k,rm.testBit k = true -> w.testBit k = !u.testBit k)) -> RepOn n rm sgs w:=by
    intro w u hu hrel
    rcases hu with (hu0 | hu1) | ⟨j,hj,pol,hev⟩
    · apply hconst_rep
      rcases hrel with heq | hneq
      · left; intro k hrmk; rw [heq k hrmk]
        have:=congrArg (fun x => x.testBit k) hu0; simp [Nat.testBit_and,hrmk] at this; exact this
      · right; intro k hrmk; rw [hneq k hrmk]
        have:=congrArg (fun x => x.testBit k) hu0; simp [Nat.testBit_and,hrmk] at this; simp [this]
    · apply hconst_rep
      rcases hrel with heq | hneq
      · right; intro k hrmk; rw [heq k hrmk]
        have:=congrArg (fun x => x.testBit k) hu1; simp [Nat.testBit_and,hrmk] at this; exact this
      · left; intro k hrmk; rw [hneq k hrmk]
        have:=congrArg (fun x => x.testBit k) hu1; simp [Nat.testBit_and,hrmk] at this; simp [this]
    · rcases hrel with heq | hneq
      · exact Or.inr ⟨j,hj,pol,fun k hk hrmk => (hev k hk hrmk).trans (heq k hrmk).symm⟩
      · refine Or.inr ⟨j,hj,!pol,fun k hk hrmk => ?_⟩
        rw [hneq k hrmk,<- hev k hk hrmk]
        cases ((sWiresFrom sgs (List.ofFn (pt n k))).getD j false) <;> cases pol <;> rfl
  have hbit_raw:∀ raw:ℕ,
      ((∀ k,rm.testBit k = true -> raw.testBit k = false) \/
       (∀ k,rm.testBit k = true -> raw.testBit k = true) \/
       (∀ k,rm.testBit k = true -> raw.testBit k = a.testBit k) \/
       (∀ k,rm.testBit k = true -> raw.testBit k = !a.testBit k) \/
       (∀ k,rm.testBit k = true -> raw.testBit k = b.testBit k) \/
       (∀ k,rm.testBit k = true -> raw.testBit k = !b.testBit k)) ->
      RepOn n rm sgs (normW (maskN n) raw):=by
    intro raw h
    rcases h with h0' | h1' | ha' | hna' | hb' | hnb'
    · apply hconst_rep
      cases hb0:raw.testBit 0
      · left; intro k hrmk; rw [testBit_normW _ _ k h0 (hmk k hrmk),hb0,h0' k hrmk]; rfl
      · right; intro k hrmk; rw [testBit_normW _ _ k h0 (hmk k hrmk),hb0,h0' k hrmk]; rfl
    · apply hconst_rep
      cases hb0:raw.testBit 0
      · right; intro k hrmk; rw [testBit_normW _ _ k h0 (hmk k hrmk),hb0,h1' k hrmk]; rfl
      · left; intro k hrmk; rw [testBit_normW _ _ k h0 (hmk k hrmk),hb0,h1' k hrmk]; rfl
    · apply hrel_rep _ a ha
      cases hb0:raw.testBit 0
      · left; intro k hrmk; rw [testBit_normW _ _ k h0 (hmk k hrmk),hb0,ha' k hrmk]; simp
      · right; intro k hrmk; rw [testBit_normW _ _ k h0 (hmk k hrmk),hb0,ha' k hrmk]; simp
    · apply hrel_rep _ a ha
      cases hb0:raw.testBit 0
      · right; intro k hrmk; rw [testBit_normW _ _ k h0 (hmk k hrmk),hb0,hna' k hrmk]; simp
      · left; intro k hrmk; rw [testBit_normW _ _ k h0 (hmk k hrmk),hb0,hna' k hrmk]; simp
    · apply hrel_rep _ b hb
      cases hb0:raw.testBit 0
      · left; intro k hrmk; rw [testBit_normW _ _ k h0 (hmk k hrmk),hb0,hb' k hrmk]; simp
      · right; intro k hrmk; rw [testBit_normW _ _ k h0 (hmk k hrmk),hb0,hb' k hrmk]; simp
    · apply hrel_rep _ b hb
      cases hb0:raw.testBit 0
      · right; intro k hrmk; rw [testBit_normW _ _ k h0 (hmk k hrmk),hb0,hnb' k hrmk]; simp
      · left; intro k hrmk; rw [testBit_normW _ _ k h0 (hmk k hrmk),hb0,hnb' k hrmk]; simp
  rcases hc with (ha0 | ha1) | (hb0 | hb1)
  · have ha_f:∀ k,rm.testBit k = true -> a.testBit k = false:=fun k hrmk => by
      have:=congrArg (fun x => x.testBit k) ha0; simp [Nat.testBit_and,hrmk] at this; exact this
    rcases op with _ | _ | _ | op <;> apply hbit_raw
    · exact Or.inl (fun k hrmk => by simp [Nat.testBit_and,ha_f k hrmk])
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (fun k hrmk => by simp [Nat.testBit_or,ha_f k hrmk])))))
    · exact Or.inl (fun k hrmk => by simp [Nat.testBit_and,ha_f k hrmk])
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (fun k hrmk => by simp [Nat.testBit_and,Nat.testBit_xor,ha_f k hrmk,hmk k hrmk])))))
  · have ha_t:∀ k,rm.testBit k = true -> a.testBit k = true:=fun k hrmk => by
      have:=congrArg (fun x => x.testBit k) ha1; simp [Nat.testBit_and,hrmk] at this; exact this
    rcases op with _ | _ | _ | op <;> apply hbit_raw
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (fun k hrmk => by simp [Nat.testBit_and,ha_t k hrmk])))))
    · exact Or.inr (Or.inl (fun k hrmk => by simp [Nat.testBit_or,ha_t k hrmk]))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (fun k hrmk => by simp [Nat.testBit_and,Nat.testBit_xor,ha_t k hrmk,hmk k hrmk])))))
    · exact Or.inl (fun k hrmk => by simp [Nat.testBit_and,Nat.testBit_xor,ha_t k hrmk,hmk k hrmk])
  · have hb_f:∀ k,rm.testBit k = true -> b.testBit k = false:=fun k hrmk => by
      have:=congrArg (fun x => x.testBit k) hb0; simp [Nat.testBit_and,hrmk] at this; exact this
    rcases op with _ | _ | _ | op <;> apply hbit_raw
    · exact Or.inl (fun k hrmk => by simp [Nat.testBit_and,hb_f k hrmk])
    · exact Or.inr (Or.inr (Or.inl (fun k hrmk => by simp [Nat.testBit_or,hb_f k hrmk])))
    · exact Or.inr (Or.inr (Or.inl (fun k hrmk => by simp [Nat.testBit_and,Nat.testBit_xor,hb_f k hrmk,hmk k hrmk])))
    · exact Or.inl (fun k hrmk => by simp [Nat.testBit_and,hb_f k hrmk])
  · have hb_t:∀ k,rm.testBit k = true -> b.testBit k = true:=fun k hrmk => by
      have:=congrArg (fun x => x.testBit k) hb1; simp [Nat.testBit_and,hrmk] at this; exact this
    rcases op with _ | _ | _ | op <;> apply hbit_raw
    · exact Or.inr (Or.inr (Or.inl (fun k hrmk => by simp [Nat.testBit_and,hb_t k hrmk])))
    · exact Or.inr (Or.inl (fun k hrmk => by simp [Nat.testBit_or,hb_t k hrmk]))
    · exact Or.inl (fun k hrmk => by simp [Nat.testBit_and,Nat.testBit_xor,hb_t k hrmk,hmk k hrmk])
    · exact Or.inr (Or.inr (Or.inr (Or.inl (fun k hrmk => by simp [Nat.testBit_and,Nat.testBit_xor,hb_t k hrmk,hmk k hrmk]))))
theorem available_add_op (n rm op a b k:ℕ) (ws:List ℕ)
    (hrm:rm &&& maskN n = rm) (ha:a ∈ ws) (hb:b ∈ ws)
    (hav:Available n rm ws k) :
    Available n rm (applyOp (maskN n) op a b :: ws) (k + 1):=by
  obtain ⟨sgs,hcl,hlen,hrep⟩:=hav
  by_cases hc:(a &&& rm = 0 \/ a &&& rm = rm) \/ (b &&& rm = 0 \/ b &&& rm = rm)
  · refine ⟨sgs,hcl,by omega,fun w hw => ?_⟩
    rcases List.mem_cons.1 hw with rfl | hw'
    · exact repOn_applyOp_same n rm op a b sgs hrm (hrep a ha) (hrep b hb) hc
    · exact hrep w hw'
  · have hna:¬ (a &&& rm = 0 \/ a &&& rm = rm):=fun h => hc (Or.inl h)
    have hnb:¬ (b &&& rm = 0 \/ b &&& rm = rm):=fun h => hc (Or.inr h)
    obtain ⟨ja,hja,pa,heva⟩:=(hrep a ha).resolve_left hna
    obtain ⟨jb,hjb,pb,hevb⟩:=(hrep b hb).resolve_left hnb
    set comb:=sOpCombine op pa pb ja jb
    have hcl':SCleanL n (sgs ++ [comb.1]):=by
      intro p g hp
      by_cases hlt:p < sgs.length
      · rw [List.getElem?_append_left hlt] at hp; exact hcl p g hp
      · rw [List.getElem?_append_right (by omega)] at hp
        have hp0:p - sgs.length = 0:=by
          have:=(List.getElem?_eq_some_iff.1 hp).1; simp at this; omega
        have hpeq:p = sgs.length:=by omega
        rw [hp0] at hp; simp at hp; subst hp; rw [hpeq]
        exact sOpCombine_clean op pa pb ja jb (n + sgs.length) hja hjb
    have h0:(maskN n).testBit 0 = true:=by rw [testBit_maskN]; simp [Nat.shiftLeft_eq]
    have hmk:∀ x,rm.testBit x = true -> (maskN n).testBit x = true:=by
      intro x hx; have:=congrArg (fun y => y.testBit x) hrm; simp [Nat.testBit_and,hx] at this; exact this
    set raw:=match op with | 0 => a &&& b | 1 => a ||| b | 2 => a &&& (b ^^^ maskN n) | _ => (a ^^^ maskN n) &&& b
    have happ:applyOp (maskN n) op a b = normW (maskN n) raw:=by
      rcases op with _ | _ | _ | op <;> rfl
    refine ⟨sgs ++ [comb.1],hcl',by simp; omega,fun w hw => ?_⟩
    rcases List.mem_cons.1 hw with rfl | hw'
    · refine Or.inr ⟨n + sgs.length,by simp,xor comb.2 (raw.testBit 0),fun x hx hrmx => ?_⟩
      rw [happ,testBit_normW (maskN n) raw x h0 (hmk x hrmx)]
      have hlen_w:(sWiresFrom sgs (List.ofFn (pt n x))).length = n + sgs.length:=by
        rw [length_sWiresFrom,List.length_ofFn]
      rw [sWiresFrom_append]
      change xor ((sWiresFrom sgs (List.ofFn (pt n x)) ++ [sOpEval comb.1.op
        ((sWiresFrom sgs (List.ofFn (pt n x))).getD comb.1.a false)
        ((sWiresFrom sgs (List.ofFn (pt n x))).getD comb.1.b false)]).getD (n + sgs.length) false)
        (xor comb.2 (raw.testBit 0)) = xor (raw.testBit x) (raw.testBit 0)
      rw [getD_snoc_len _ _ _ _ hlen_w]
      have hca:comb.1.a = ja:=by rcases op with _ | _ | _ | op <;> cases pa <;> cases pb <;> rfl
      have hcb:comb.1.b = jb:=by rcases op with _ | _ | _ | op <;> cases pa <;> cases pb <;> rfl
      rw [hca,hcb]
      have hce:=sOpCombine_eval op pa pb
        ((sWiresFrom sgs (List.ofFn (pt n x))).getD ja false)
        ((sWiresFrom sgs (List.ofFn (pt n x))).getD jb false) ja jb
      rw [heva x hx hrmx,hevb x hx hrmx] at hce
      have hrawx:sOpEval op (a.testBit x) (b.testBit x) = raw.testBit x:=by
        rcases op with _ | _ | _ | op <;>
          simp [raw,sOpEval,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,hmk x hrmx]
      rw [hrawx] at hce
      rw [<- hce]
      cases (sOpEval comb.1.op ((sWiresFrom sgs (List.ofFn (pt n x))).getD ja false)
        ((sWiresFrom sgs (List.ofFn (pt n x))).getD jb false)) <;> cases comb.2 <;> cases raw.testBit 0 <;> rfl
    · rcases hrep w hw' with hc' | ⟨j,hj,pol,hev'⟩
      · exact Or.inl hc'
      · refine Or.inr ⟨j,by simp; omega,pol,fun x hx hrmx => ?_⟩
        rw [sWiresFrom_append,getD_sWiresFrom [comb.1] _ j (by rw [length_sWiresFrom,List.length_ofFn]; exact hj)]
        exact hev' x hx hrmx
theorem available_step_slice (n op a b kc k:ℕ) (sl:SliceData) (ws:List ℕ)
    (hrm:sl.rm &&& maskN n = sl.rm)
    (hlow:sl.rm &&& sl.low ≠ 0)
    (hbase:∀ b' ∈ sl.base,∃ i < n,projSl sl (inpW n i) = b')
    (ha:a ∈ ws) (hb:b ∈ ws)
    (hav:Available n sl.rm ws k) :
    let z:=applyOp (maskN n) op a b
    let pr:=projSl sl z
    let zA:=if pr != 0 && !sl.base.contains pr then 1 else 0
    Available n sl.rm (mkCand ws a b z kc) (k + zA):=by
  intro z pr zA
  by_cases hadd:zA = 1
  · rw [hadd]
    obtain ⟨sgs,hcl,hlen,hrep⟩:=available_add_op n sl.rm op a b k ws hrm ha hb hav
    refine ⟨sgs,hcl,hlen,fun w hw => ?_⟩
    rcases mkCand_subset ha hb w hw with rfl | hw'
    · exact hrep z List.mem_cons_self
    · exact hrep w (List.mem_cons_of_mem _ hw')
  · have hzA0:zA = 0:=by dsimp only [zA] at hadd ⊢; split_ifs at hadd ⊢ <;> omega
    rw [hzA0,Nat.add_zero]
    obtain ⟨sgs,hcl,hlen,hrep⟩:=hav
    refine ⟨sgs,hcl,hlen,fun w hw => ?_⟩
    rcases mkCand_subset ha hb w hw with rfl | hw'
    ·
      by_cases hpr0:pr = 0
      · exact Or.inl ((projSl_eq_zero_iff sl hlow z).1 hpr0)
      · have hmem_b:pr ∈ sl.base:=by
          dsimp only [zA] at hzA0
          cases hc:sl.base.contains pr with
          | true => exact List.mem_of_elem_eq_true hc
          | false =>
            have hcond:(pr != 0 && !sl.base.contains pr) = true:=by rw [hc]; simp [hpr0]
            simp only [hcond,↓reduceIte] at hzA0
            cases hzA0
        obtain ⟨i,hin,hi_eq⟩:=hbase pr hmem_b
        rcases projSl_eq_iff n sl hrm z (inpW n i) hi_eq.symm hpr0 with heq | hneq
        · refine Or.inr ⟨i,by omega,false,fun x hx hrmx => ?_⟩
          rw [Bool.xor_false,getD_sWiresFrom _ _ i (by simp [hin]),ofFn_pt_getD n x i hin,
              heq x hx hrmx,inpW_testBit n i x hx]
        · refine Or.inr ⟨i,by omega,true,fun x hx hrmx => ?_⟩
          rw [Bool.xor_true,getD_sWiresFrom _ _ i (by simp [hin]),ofFn_pt_getD n x i hin,
              hneq x hx hrmx,inpW_testBit n i x hx]
    · exact hrep w hw'
def countConst (sl:SliceData) (ws:List ℕ):ℕ :=
  (ws.filter (fun w => projSl sl w == 0)).length
theorem countConst_perm (sl:SliceData) {ws ws':List ℕ} (hp:ws.Perm ws') :
    countConst sl ws = countConst sl ws' :=
  (hp.filter _).length_eq
theorem srun_available_sound (n tgt:ℕ) (sl:SliceData)
    (hrm:sl.rm &&& maskN n = sl.rm)
    (hlow:sl.rm &&& sl.low ≠ 0)
    (hnc_tgt:projSl sl tgt ≠ 0) :
    ∀ s ws,SRun (maskN n) tgt s ws ->
      ∀ k,Available n sl.rm ws k ->
        ∃ r,r + countConst sl ws ≤ k + s /\ HasSignedOn n sl.rm tgt r:=by
  intro s ws hrun
  induction hrun with
  | done s =>
    intro k hav
    obtain ⟨sgs,hcl,hlen,hrep⟩:=hav
    have hnotc:¬ (tgt &&& sl.rm = 0 \/ tgt &&& sl.rm = sl.rm):=by
      intro h; exact hnc_tgt ((projSl_eq_zero_iff sl hlow tgt).2 h)
    obtain ⟨o,ho,pol,hev⟩:=(hrep tgt List.mem_cons_self).resolve_left hnotc
    have hcc:countConst sl [tgt] = 0:=by simp [countConst,hnc_tgt]
    exact ⟨k,by rw [hcc]; omega,sgs,o,pol,hcl,hlen,ho,hev⟩
  | perm hperm _ ih =>
    intro k hav
    rw [<- countConst_perm sl hperm]
    exact ih k (available_perm hperm.symm hav)
  | step s ws a b op kc hnd ha hb hab _ _ _ _ hz _ _ ih =>
    intro k hav
    set z:=applyOp (maskN n) op a b
    set cw:=mkCand ws a b z kc
    have hcc_eq:∀ (P:ℕ -> Bool),
        (cw.filter P).length + (if kc == 0 || kc == 2 then (if P a then 1 else 0) else 0) +
          (if kc == 0 || kc == 1 then (if P b then 1 else 0) else 0) =
        (ws.filter P).length + (if P z then 1 else 0):=by
      intro P
      have her1:(ws.erase a).length + 1 = ws.length:=by
        have:=List.length_erase_of_mem ha; have:=List.length_pos_of_mem ha; omega
      have hperm_ws:ws.Perm (a :: b :: ((ws.erase a).erase b)):=by
        have hp1:ws.Perm (a :: ws.erase a):=List.perm_cons_erase ha
        have hb':b ∈ ws.erase a:=(List.mem_erase_of_ne (Ne.symm hab)).2 hb
        have hp2:(ws.erase a).Perm (b :: (ws.erase a).erase b):=List.perm_cons_erase hb'
        exact hp1.trans (hp2.cons a)
      have hws_f:=(hperm_ws.filter P).length_eq
      simp only [List.filter_cons] at hws_f
      rcases kc with _ | _ | _ | kc <;>
        simp only [cw,mkCand,List.filter_append,List.filter_cons,
          List.filter_nil,List.length_append,List.length_cons,List.length_nil] <;>
        cases hpa:P a <;> cases hpb:P b <;> cases hpz:P z <;>
        simp [hpa,hpb,hpz] at hws_f ⊢ <;> omega
    set P:ℕ -> Bool:=fun w => projSl sl w == 0
    have hcc_step:=hcc_eq P
    change countConst sl cw + _ + _ = countConst sl ws + _ at hcc_step
    by_cases hca:P a = true
    ·
      have ha_c:a &&& sl.rm = 0 \/ a &&& sl.rm = sl.rm :=
        (projSl_eq_zero_iff sl hlow a).1 (of_decide_eq_true (by simpa [P] using hca))
      have hav':Available n sl.rm cw k:=by
        obtain ⟨sgs,hcl,hlen,hrep⟩:=hav
        refine ⟨sgs,hcl,hlen,fun w hw => ?_⟩
        rcases mkCand_subset ha hb w hw with rfl | hw'
        · exact repOn_applyOp_same n sl.rm op a b sgs hrm (hrep a ha) (hrep b hb) (Or.inl ha_c)
        · exact hrep w hw'
      obtain ⟨r,hr,hsig⟩:=ih k hav'
      refine ⟨r,?_,hsig⟩
      by_cases hcb:P b = true
      ·
        have hb_c:b &&& sl.rm = 0 \/ b &&& sl.rm = sl.rm :=
          (projSl_eq_zero_iff sl hlow b).1 (of_decide_eq_true (by simpa [P] using hcb))
        have hzc:z &&& sl.rm = 0 \/ z &&& sl.rm = sl.rm:=by
          have h0:(maskN n).testBit 0 = true:=by rw [testBit_maskN]; simp [Nat.shiftLeft_eq]
          have hmk:∀ x,sl.rm.testBit x = true -> (maskN n).testBit x = true:=by
            intro x hx; have:=congrArg (fun y => y.testBit x) hrm; simp [Nat.testBit_and,hx] at this; exact this
          have hconst:∀ f:Bool,(∀ x,sl.rm.testBit x = true -> z.testBit x = f) -> z &&& sl.rm = 0 \/ z &&& sl.rm = sl.rm:=by
            intro f hf
            cases f
            · left; apply Nat.eq_of_testBit_eq; intro x; simp only [Nat.testBit_and,Nat.zero_testBit]
              cases hrx:sl.rm.testBit x; simp; simp [hf x hrx]
            · right; apply Nat.eq_of_testBit_eq; intro x; simp only [Nat.testBit_and]
              cases hrx:sl.rm.testBit x; simp; simp [hf x hrx]
          have hraw:∀ ca cb:Bool,
              (∀ x,sl.rm.testBit x = true -> a.testBit x = ca) ->
              (∀ x,sl.rm.testBit x = true -> b.testBit x = cb) ->
              z &&& sl.rm = 0 \/ z &&& sl.rm = sl.rm:=by
            intro ca cb hfa hfb
            set raw:=match op with | 0 => a &&& b | 1 => a ||| b | 2 => a &&& (b ^^^ maskN n) | _ => (a ^^^ maskN n) &&& b
            have happ:z = normW (maskN n) raw:=by rcases op with _ | _ | _ | op <;> rfl
            apply hconst (xor (sOpEval op ca cb) (raw.testBit 0))
            intro x hrx
            rw [happ,testBit_normW (maskN n) raw x h0 (hmk x hrx)]
            congr 1
            rcases op with _ | _ | _ | op <;>
              simp [raw,sOpEval,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,hfa x hrx,hfb x hrx,hmk x hrx]
          rcases ha_c with ha0 | ha1 <;> rcases hb_c with hb0 | hb1
          · exact hraw false false (fun x hrx => by have:=congrArg (fun y => y.testBit x) ha0; simp [Nat.testBit_and,hrx] at this; exact this)
              (fun x hrx => by have:=congrArg (fun y => y.testBit x) hb0; simp [Nat.testBit_and,hrx] at this; exact this)
          · exact hraw false true (fun x hrx => by have:=congrArg (fun y => y.testBit x) ha0; simp [Nat.testBit_and,hrx] at this; exact this)
              (fun x hrx => by have:=congrArg (fun y => y.testBit x) hb1; simp [Nat.testBit_and,hrx] at this; exact this)
          · exact hraw true false (fun x hrx => by have:=congrArg (fun y => y.testBit x) ha1; simp [Nat.testBit_and,hrx] at this; exact this)
              (fun x hrx => by have:=congrArg (fun y => y.testBit x) hb0; simp [Nat.testBit_and,hrx] at this; exact this)
          · exact hraw true true (fun x hrx => by have:=congrArg (fun y => y.testBit x) ha1; simp [Nat.testBit_and,hrx] at this; exact this)
              (fun x hrx => by have:=congrArg (fun y => y.testBit x) hb1; simp [Nat.testBit_and,hrx] at this; exact this)
        have hcz:P z = true:=by simp [P,(projSl_eq_zero_iff sl hlow z).2 hzc]
        simp only [hca,hcb,hcz,↓reduceIte] at hcc_step
        split_ifs at hcc_step <;> omega
      · have hcb':P b = false:=Bool.eq_false_iff.2 hcb
        simp only [hca,hcb',Bool.false_eq_true,↓reduceIte,Nat.add_zero] at hcc_step
        split_ifs at hcc_step <;> omega
    · have hca':P a = false:=Bool.eq_false_iff.2 hca
      by_cases hcb:P b = true
      ·
        have hb_c:b &&& sl.rm = 0 \/ b &&& sl.rm = sl.rm :=
          (projSl_eq_zero_iff sl hlow b).1 (of_decide_eq_true (by simpa [P] using hcb))
        have hav':Available n sl.rm cw k:=by
          obtain ⟨sgs,hcl,hlen,hrep⟩:=hav
          refine ⟨sgs,hcl,hlen,fun w hw => ?_⟩
          rcases mkCand_subset ha hb w hw with rfl | hw'
          · exact repOn_applyOp_same n sl.rm op a b sgs hrm (hrep a ha) (hrep b hb) (Or.inr hb_c)
          · exact hrep w hw'
        obtain ⟨r,hr,hsig⟩:=ih k hav'
        refine ⟨r,?_,hsig⟩
        simp only [hca',hcb,Bool.false_eq_true,↓reduceIte,Nat.add_zero] at hcc_step
        split_ifs at hcc_step <;> omega
      ·
        have hcb':P b = false:=Bool.eq_false_iff.2 hcb
        have hav':Available n sl.rm cw (k + 1):=by
          obtain ⟨sgs,hcl,hlen,hrep⟩:=available_add_op n sl.rm op a b k ws hrm ha hb hav
          refine ⟨sgs,hcl,hlen,fun w hw => ?_⟩
          rcases mkCand_subset ha hb w hw with rfl | hw'
          · exact hrep z List.mem_cons_self
          · exact hrep w (List.mem_cons_of_mem _ hw')
        obtain ⟨r,hr,hsig⟩:=ih (k + 1) hav'
        refine ⟨r,?_,hsig⟩
        simp only [hca',hcb',Bool.false_eq_true,↓reduceIte,Nat.add_zero] at hcc_step
        split_ifs at hcc_step <;> omega
inductive BT (α:Type) where
  | leaf:Option α -> BT α
  | node:BT α -> BT α -> BT α
deriving Repr
def btGet {α:Type}:BT α -> ℕ -> Option α
  | BT.leaf x,_ => x
  | BT.node l r,i => if i &&& 1 == 0 then btGet l (i >>> 1) else btGet r (i >>> 1)
def btAll {α:Type} (P:α -> Bool):BT α -> Bool
  | BT.leaf none => true
  | BT.leaf (some x) => P x
  | BT.node l r => btAll P l && btAll P r
theorem btAll_sound {α:Type} (P:α -> Bool) (t:BT α) (h:btAll P t = true) :
    ∀ i x,btGet t i = some x -> P x = true:=by
  induction t with
  | leaf o =>
    intro i x hx
    cases o with
    | none => cases hx
    | some y =>
      simp only [btGet] at hx; injection hx with hxy; subst hxy
      simpa [btAll] using h
  | node l r ihl ihr =>
    intro i x hx
    simp only [btAll,Bool.and_eq_true] at h
    unfold btGet at hx
    split_ifs at hx
    · exact ihl h.1 (i >>> 1) x hx
    · exact ihr h.2 (i >>> 1) x hx
def swapVar (mSame m10 m01 shift w:ℕ):ℕ :=
  (w &&& mSame) ||| ((w &&& m10) >>> shift) ||| ((w &&& m01) <<< shift)
theorem swapVar_zero (mSame m10 m01 shift:ℕ):swapVar mSame m10 m01 shift 0 = 0:=by
  simp [swapVar]
theorem swapVar_or (mSame m10 m01 shift u v:ℕ) :
    swapVar mSame m10 m01 shift (u ||| v) =
    swapVar mSame m10 m01 shift u ||| swapVar mSame m10 m01 shift v:=by
  apply Nat.eq_of_testBit_eq; intro k
  simp only [swapVar,Nat.testBit_or,Nat.testBit_and,Nat.testBit_shiftRight,Nat.testBit_shiftLeft]
  cases u.testBit k <;> cases v.testBit k <;> cases mSame.testBit k <;>
  cases u.testBit (shift + k) <;> cases v.testBit (shift + k) <;> cases m10.testBit (shift + k) <;>
  cases decide (shift ≤ k) <;>
  cases u.testBit (k - shift) <;> cases v.testBit (k - shift) <;> cases m01.testBit (k - shift) <;> rfl
def actSwaps (swaps:List (ℕ × ℕ × ℕ × ℕ)) (w:ℕ):ℕ :=
  swaps.foldl (fun acc s => swapVar s.1 s.2.1 s.2.2.1 s.2.2.2 acc) w
theorem actSwaps_zero (swaps:List (ℕ × ℕ × ℕ × ℕ)):actSwaps swaps 0 = 0:=by
  unfold actSwaps
  induction swaps with
  | nil => rfl
  | cons s sw ih => simp only [List.foldl_cons,swapVar_zero]; exact ih
theorem actSwaps_or (swaps:List (ℕ × ℕ × ℕ × ℕ)) :
    ∀ u v,actSwaps swaps (u ||| v) = actSwaps swaps u ||| actSwaps swaps v:=by
  unfold actSwaps
  induction swaps with
  | nil => intro u v; rfl
  | cons s sw ih =>
    intro u v
    simp only [List.foldl_cons,swapVar_or]
    exact ih _ _
structure SymData where
  vp:Array ℕ
  invVp:Array ℕ
  bm:Array ℕ
  invBm:Array ℕ
  swaps:List (ℕ × ℕ × ℕ × ℕ)
  invSlice:BT ℕ
deriving Repr
def actWAux (bm:Array ℕ) (w:ℕ):ℕ -> ℕ -> ℕ
  | 0,acc => acc
  | x + 1,acc => actWAux bm w x (if w.testBit x then acc ||| (1 <<< bm.getD x 0) else acc)
def actW (R:ℕ) (bm:Array ℕ) (w:ℕ):ℕ:=actWAux bm w R 0
theorem actWAux_testBit (bm:Array ℕ) (w:ℕ) (y:ℕ) :
    ∀ x acc,
      (actWAux bm w x acc).testBit y =
      (acc.testBit y || (List.range x).any (fun k => w.testBit k && decide (bm.getD k 0 = y))):=by
  intro x
  induction x with
  | zero => intro acc; simp [actWAux]
  | succ x ih =>
    intro acc
    simp only [actWAux,ih,List.range_succ,List.any_append,List.any_cons,List.any_nil,Bool.or_false]
    cases hw:w.testBit x with
    | false => simp
    | true =>
      simp only [↓reduceIte,Nat.testBit_or,Bool.true_and,testBit_one_shiftLeft]
      have hcomm:decide (y = bm.getD x 0) = decide (bm.getD x 0 = y):=decide_eq_decide.2 eq_comm
      rw [hcomm]
      cases acc.testBit y <;> cases decide (bm.getD x 0 = y) <;>
        cases ((List.range x).any fun k => w.testBit k && decide (bm.getD k 0 = y)) <;> rfl
theorem actW_testBit_bij (n:ℕ) (bm invBm:Array ℕ)
    (hbij:∀ x < 1 <<< n,
      bm.getD x 0 < 1 <<< n /\ invBm.getD x 0 < 1 <<< n /\
      invBm.getD (bm.getD x 0) 0 = x /\ bm.getD (invBm.getD x 0) 0 = x)
    (w y:ℕ) :
    (actW (1 <<< n) bm w).testBit y =
      (decide (y < 1 <<< n) && w.testBit (invBm.getD y 0)):=by
  unfold actW
  rw [actWAux_testBit]
  simp only [Nat.zero_testBit,Bool.false_or]
  by_cases hy:y < 1 <<< n
  · simp only [hy,decide_true,Bool.true_and]
    obtain ⟨_,hinv_lt,_,hbi⟩:=hbij y hy
    cases hw:w.testBit (invBm.getD y 0) with
    | true =>
      rw [List.any_eq_true]
      refine ⟨invBm.getD y 0,List.mem_range.2 hinv_lt,?_⟩
      simp only [Bool.and_eq_true,decide_eq_true_eq]
      exact ⟨hw,hbi⟩
    | false =>
      rw [List.any_eq_false]
      intro k hk
      rw [List.mem_range] at hk
      simp only [Bool.and_eq_true,decide_eq_true_eq,not_and]
      intro hwk heq
      have h1:=(hbij k hk).2.2.1
      rw [heq] at h1
      rw [h1] at hw
      rw [hwk] at hw
      cases hw
  · simp only [hy,decide_false,Bool.false_and]
    rw [List.any_eq_false]
    intro k hk
    rw [List.mem_range] at hk
    have hlt:=(hbij k hk).1
    simp only [Bool.and_eq_true,decide_eq_true_eq,not_and]
    intro _ heq; omega
theorem actSwaps_eq_actW (n:ℕ) (bm:Array ℕ) (swaps:List (ℕ × ℕ × ℕ × ℕ))
    (hbasis:∀ x < 1 <<< n,actSwaps swaps (1 <<< x) = 1 <<< bm.getD x 0)
    (w:ℕ) (hw:w &&& maskN n = w) :
    actSwaps swaps w = actW (1 <<< n) bm w:=by
  have hw_enc:w = encBAux w.testBit (1 <<< n):=by
    apply Nat.eq_of_testBit_eq; intro k
    rw [encBAux_testBit]
    by_cases hk:k < 1 <<< n
    · simp [hk]
    · have hmk:(maskN n).testBit k = false:=by rw [testBit_maskN]; simp [hk]
      have h1:=congrArg (fun x => x.testBit k) hw
      simp [Nat.testBit_and,hmk] at h1
      simp [hk,h1]
  have haux:∀ m ≤ 1 <<< n,∀ acc,
      actSwaps swaps (encBAux w.testBit m) ||| acc = actWAux bm w m acc:=by
    intro m
    induction m with
    | zero => intro _ acc; simp [encBAux,actSwaps_zero,actWAux]
    | succ m ih =>
      intro hm acc
      simp only [encBAux,actSwaps_or,actWAux]
      cases hwm:w.testBit m with
      | false =>
        simp only [Bool.false_eq_true,↓reduceIte,actSwaps_zero,Nat.or_zero]
        exact ih (by omega) acc
      | true =>
        simp only [↓reduceIte,hbasis m (by omega)]
        rw [Nat.or_assoc,Nat.or_comm (1 <<< bm.getD m 0) acc]
        exact ih (by omega) (acc ||| (1 <<< bm.getD m 0))
  conv_lhs => rw [hw_enc]
  have:=haux (1 <<< n) (le_refl _) 0
  simpa [actW] using this
def symOK (n tgt nSlices:ℕ) (slices:BT SliceData) (sd:SymData):Bool :=
  let R:=1 <<< n
  (sd.vp.size == n) && (sd.invVp.size == n) &&
  (sd.bm.size == R) && (sd.invBm.size == R) &&
  (sd.bm.getD 0 1 == 0) &&
  (List.range R).all (fun x =>
    let bx:=sd.bm.getD x 0
    let ix:=sd.invBm.getD x 0
    (bx < R) && (ix < R) && (sd.invBm.getD bx 0 == x) && (sd.bm.getD ix 0 == x) &&
    (actSwaps sd.swaps (1 <<< x) == 1 <<< bx)) &&
  (List.range n).all (fun i =>
    let vi:=sd.vp.getD i 0
    let ivi:=sd.invVp.getD i 0
    (vi < n) && (ivi < n) && (sd.invVp.getD vi 0 == i) && (sd.vp.getD ivi 0 == i)) &&
  (List.range R).all (fun x =>
    (List.range n).all (fun i =>
      (sd.invBm.getD x 0).testBit i == x.testBit (sd.vp.getD i 0))) &&
  (actSwaps sd.swaps tgt == tgt) &&
  (List.range nSlices).all (fun dri =>
    match btGet sd.invSlice dri,btGet slices dri with
    | some ri,some slD =>
      match btGet slices ri with
      | some slR => (ri < nSlices) && (actSwaps sd.swaps slR.rm == slD.rm)
      | none => false
    | _,_ => false)
theorem actW_comm_ops (n:ℕ) (sd:SymData)
    (hbij:∀ x < 1 <<< n,
      sd.bm.getD x 0 < 1 <<< n /\ sd.invBm.getD x 0 < 1 <<< n /\
      sd.invBm.getD (sd.bm.getD x 0) 0 = x /\ sd.bm.getD (sd.invBm.getD x 0) 0 = x)
    (hbm0:sd.bm.getD 0 0 = 0) :
    let act:=actW (1 <<< n) sd.bm
    act 0 = 0 /\
    act (maskN n) = maskN n /\
    (∀ a b,act a = act b -> a &&& maskN n = a -> b &&& maskN n = b -> a = b) /\
    (∀ op a b,act (applyOp (maskN n) op a b) = applyOp (maskN n) op (act a) (act b)):=by
  intro act
  have hinv0:sd.invBm.getD 0 0 = 0:=by
    have:=(hbij 0 (by simp [Nat.shiftLeft_eq])).2.2.1
    rwa [hbm0] at this
  have h0mask:(maskN n).testBit 0 = true:=by rw [testBit_maskN]; simp [Nat.shiftLeft_eq]
  have hact_tb:∀ w y,(act w).testBit y = (decide (y < 1 <<< n) && w.testBit (sd.invBm.getD y 0)) :=
    actW_testBit_bij n sd.bm sd.invBm hbij
  refine ⟨?_,?_,?_,?_⟩
  · apply Nat.eq_of_testBit_eq; intro y; simp [hact_tb]
  · apply Nat.eq_of_testBit_eq; intro y
    rw [hact_tb,testBit_maskN,testBit_maskN]
    by_cases hy:y < 1 <<< n
    · simp only [hy,decide_true,Bool.true_and,(hbij y hy).2.1]
    · simp only [hy,decide_false,Bool.false_and]
  · intro a b hab ha hb
    apply Nat.eq_of_testBit_eq; intro x
    by_cases hx:x < 1 <<< n
    · have hbx:=(hbij x hx).1
      have h1:=congrArg (fun u => u.testBit (sd.bm.getD x 0)) hab
      rw [hact_tb,hact_tb] at h1
      simp only [hbx,decide_true,Bool.true_and,(hbij x hx).2.2.1] at h1
      exact h1
    · have hmk:(maskN n).testBit x = false:=by rw [testBit_maskN]; simp [hx]
      have ha':=congrArg (fun u => u.testBit x) ha
      have hb':=congrArg (fun u => u.testBit x) hb
      simp [Nat.testBit_and,hmk] at ha' hb'
      rw [ha',hb']
  · intro op a b
    apply Nat.eq_of_testBit_eq; intro y
    by_cases hy:y < 1 <<< n
    · have hmy:(maskN n).testBit y = true:=by rw [testBit_maskN]; simp [hy]
      have hiy:sd.invBm.getD y 0 < 1 <<< n:=(hbij y hy).2.1
      have hmiy:(maskN n).testBit (sd.invBm.getD y 0) = true:=by rw [testBit_maskN]; exact decide_eq_true hiy
      have h0lt:0 < 1 <<< n:=by rw [Nat.shiftLeft_eq,Nat.one_mul]; exact Nat.two_pow_pos n
      rw [hact_tb]
      simp only [hy,decide_true,Bool.true_and]
      rcases op with _ | _ | _ | op <;>
        simp only [applyOp,testBit_normW (maskN n) _ _ h0mask hmy,testBit_normW (maskN n) _ _ h0mask hmiy,
          Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,hact_tb,hy,h0lt,decide_true,Bool.true_and,
          hmy,hmiy,h0mask,hinv0]
    · have hmy:(maskN n).testBit y = false:=by rw [testBit_maskN]; simp [hy]
      rw [hact_tb]; simp only [hy,decide_false,Bool.false_and]
      symm
      set aa:=act a
      set ab:=act b
      have hay:aa.testBit y = false:=by rw [show aa = act a from rfl,hact_tb]; simp [hy]
      have hby:ab.testBit y = false:=by rw [show ab = act b from rfl,hact_tb]; simp [hy]
      rcases op with _ | _ | _ | op <;>
      · unfold applyOp normW; split_ifs <;> simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,hay,hby,hmy] <;> rfl
theorem srun_actW (n tgt:ℕ) (sd:SymData)
    (hbij:∀ x < 1 <<< n,
      sd.bm.getD x 0 < 1 <<< n /\ sd.invBm.getD x 0 < 1 <<< n /\
      sd.invBm.getD (sd.bm.getD x 0) 0 = x /\ sd.bm.getD (sd.invBm.getD x 0) 0 = x)
    (hbm0:sd.bm.getD 0 0 = 0)
    (htgt:actW (1 <<< n) sd.bm tgt = tgt) :
    ∀ s ws,(∀ w ∈ ws,w &&& maskN n = w) ->
      SRun (maskN n) tgt s ws ->
      SRun (maskN n) tgt s (ws.map (actW (1 <<< n) sd.bm)):=by
  obtain ⟨hact0,hactM,hactInj,hactOp⟩:=actW_comm_ops n sd hbij hbm0
  set act:=actW (1 <<< n) sd.bm
  intro s ws hmask hrun
  induction hrun with
  | done s =>
    simp only [List.map_cons,List.map_nil,show act tgt = tgt from htgt]
    exact SRun.done s
  | perm hperm _ ih =>
    exact SRun.perm (hperm.map act) (ih (fun w hw => hmask w (hperm.subset hw)))
  | step s ws a b op kc hnd ha hb hab hop hkc hz0 hzM hzn hcw_len _ ih =>
    have hact_nodup:(ws.map act).Nodup:=by
      apply List.Nodup.map_on _ hnd
      intro u hu v hv heq; exact hactInj u v heq (hmask u hu) (hmask v hv)
    have hzm:applyOp (maskN n) op a b &&& maskN n = applyOp (maskN n) op a b:=by
      have hmk_a:=hmask a ha; have hmk_b:=hmask b hb
      rcases op with _ | _ | _ | op <;>
      · apply normW_le_mask; apply Nat.eq_of_testBit_eq; intro k
        have hka:=congrArg (fun x => x.testBit k) hmk_a
        have hkb:=congrArg (fun x => x.testBit k) hmk_b
        simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor] at hka hkb ⊢
        cases hmk':(maskN n).testBit k <;> simp [hmk'] at hka hkb ⊢ <;> simp [hka,hkb]
    have hcw_mask:∀ w ∈ mkCand ws a b (applyOp (maskN n) op a b) kc,w &&& maskN n = w:=by
      intro w hw
      rcases mkCand_subset ha hb w hw with rfl | hw'
      · exact hzm
      · exact hmask w hw'
    have hmap_er:∀ (L:List ℕ) (x:ℕ),L.Nodup -> (∀ w ∈ L,w &&& maskN n = w) -> x &&& maskN n = x ->
        (L.erase x).map act = (L.map act).erase (act x):=by
      intro L x hndL hmL hxm
      induction L with
      | nil => simp
      | cons y L ihl =>
        obtain ⟨hyL,hndL'⟩:=List.nodup_cons.1 hndL
        by_cases hxy:y = x
        · subst hxy; simp
        · have hne:act y ≠ act x:=fun h => hxy (hactInj y x h (hmL y List.mem_cons_self) hxm)
          simp only [List.erase_cons_tail (by simp [hxy]:¬ (y == x) = true),List.map_cons,
            List.erase_cons_tail (by simp [hne]:¬ (act y == act x) = true)]
          rw [ihl hndL' (fun w hw => hmL w (List.mem_cons_of_mem _ hw))]
    have hmap_cand:(mkCand ws a b (applyOp (maskN n) op a b) kc).map act =
        mkCand (ws.map act) (act a) (act b) (applyOp (maskN n) op (act a) (act b)) kc:=by
      have her1:=hmap_er ws a hnd hmask (hmask a ha)
      have her2:=hmap_er (ws.erase a) b (hnd.erase a)
        (fun w hw => hmask w (List.mem_of_mem_erase hw)) (hmask b hb)
      rw [her1] at her2
      rcases kc with _ | _ | _ | kc <;>
        simp [mkCand,List.map_append,her2,hactOp op a b]
    have hab':act a ≠ act b:=fun h => hab (hactInj a b h (hmask a ha) (hmask b hb))
    have hz0':applyOp (maskN n) op (act a) (act b) ≠ 0:=by
      rw [<- hactOp op a b]; intro h; exact hz0 (hactInj _ 0 (h.trans hact0.symm) hzm (by simp))
    have hzM':applyOp (maskN n) op (act a) (act b) ≠ maskN n:=by
      rw [<- hactOp op a b]; intro h; exact hzM (hactInj _ (maskN n) (h.trans hactM.symm) hzm (by simp))
    have hzn':applyOp (maskN n) op (act a) (act b) ∉ ws.map act:=by
      rw [<- hactOp op a b]; intro hmem
      obtain ⟨w,hw,heq⟩:=List.mem_map.1 hmem
      have:=hactInj w _ heq (hmask w hw) hzm
      exact hzn (this ▸ hw)
    apply SRun.step s (ws.map act) (act a) (act b) op kc hact_nodup
      (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) hab' hop hkc hz0' hzM' hzn'
    · rw [<- hmap_cand,List.length_map]; exact hcw_len
    · rw [<- hmap_cand]; exact ih hcw_mask
theorem available_actW (n rm k:ℕ) (sd:SymData) (cw:List ℕ)
    (hbij:∀ x < 1 <<< n,
      sd.bm.getD x 0 < 1 <<< n /\ sd.invBm.getD x 0 < 1 <<< n /\
      sd.invBm.getD (sd.bm.getD x 0) 0 = x /\ sd.bm.getD (sd.invBm.getD x 0) 0 = x)
    (hvp_lt:∀ i < n,sd.vp.getD i 0 < n)
    (hbit:∀ x < 1 <<< n,∀ i < n,(sd.invBm.getD x 0).testBit i = x.testBit (sd.vp.getD i 0))
    (hav:Available n rm cw k) :
    Available n (actW (1 <<< n) sd.bm rm) (cw.map (actW (1 <<< n) sd.bm)) k:=by
  set act:=actW (1 <<< n) sd.bm
  have hact_tb:∀ w y,(act w).testBit y = (decide (y < 1 <<< n) && w.testBit (sd.invBm.getD y 0)) :=
    actW_testBit_bij n sd.bm sd.invBm hbij
  obtain ⟨sgs,hcl,hlen,hrep⟩:=hav
  set init:List SStat:=(List.range n).map (fun i => Sum.inr (sd.vp.getD i 0,false))
  set res:=sSubst n sgs (init,[])
  have hinit_len:init.length = n:=by simp [init]
  have hinit_get:∀ i,init.getD i (Sum.inl false) =
      if i < n then Sum.inr (sd.vp.getD i 0,false) else Sum.inl false:=by
    intro i
    by_cases hi:i < n
    · simp [init,List.getD_eq_getElem?_getD,hi]
    · rw [List.getD_eq_default _ _ (by simp [init]; omega)]; simp [hi]
  have hcl':SCleanL n res.2:=by
    apply sSubst_clean n sgs (init,[])
    · intro i; rw [hinit_get]; split_ifs with hi; exact hvp_lt i hi; trivial
    · intro p g hp; simp at hp
  have hlen':res.2.length ≤ k:=by
    have h1:res.2.length ≤ 0 + sgs.length:=sSubst_len n sgs (init,[])
    omega
  have hinv:∀ y < 1 <<< n,
      SInv n (List.ofFn (pt n y)) (sWiresFrom sgs (List.ofFn (pt n (sd.invBm.getD y 0)))) res:=by
    intro y hy
    apply sInv_subst n (List.ofFn (pt n y)) (by simp) sgs _ (init,[])
    refine ⟨by simp [hinit_len],fun i => ?_⟩
    rw [hinit_get]
    by_cases hi:i < n
    · simp only [hi,↓reduceIte,sStatValid,sStatVal,sWiresFrom,List.foldl_nil,Bool.xor_false,
        List.length_nil,Nat.add_zero,hvp_lt i hi,true_and,ofFn_pt_getD n y _ (hvp_lt i hi),ofFn_pt_getD n _ i hi]
      exact (hbit y hy i hi).symm
    · simp only [hi,↓reduceIte,sStatValid,sStatVal,true_and]
      rw [List.getD_eq_default _ _ (by simp; omega)]
  refine ⟨res.2,hcl',hlen',fun w hw => ?_⟩
  obtain ⟨u,hu,rfl⟩:=List.mem_map.1 hw
  rcases hrep u hu with (hu0 | hu1) | ⟨j,hj,pol,hevu⟩
  · left; left
    apply Nat.eq_of_testBit_eq; intro y
    simp only [Nat.testBit_and,Nat.zero_testBit,hact_tb]
    by_cases hy:y < 1 <<< n
    · have:=congrArg (fun x => x.testBit (sd.invBm.getD y 0)) hu0
      simp only [Nat.testBit_and,Nat.zero_testBit] at this
      simp only [hy,decide_true,Bool.true_and]
      exact this
    · simp only [hy,decide_false,Bool.false_and]
  · left; right
    apply Nat.eq_of_testBit_eq; intro y
    simp only [Nat.testBit_and,hact_tb]
    by_cases hy:y < 1 <<< n
    · have:=congrArg (fun x => x.testBit (sd.invBm.getD y 0)) hu1
      simp only [Nat.testBit_and] at this
      simp only [hy,decide_true,Bool.true_and]
      exact this
    · simp only [hy,decide_false,Bool.false_and]
  · cases hst:res.1.getD j (Sum.inl false) with
    | inl c =>
      left
      cases hcp:xor c pol with
      | false =>
        left; apply Nat.eq_of_testBit_eq; intro y
        simp only [Nat.testBit_and,Nat.zero_testBit,hact_tb]
        by_cases hy:y < 1 <<< n
        · simp only [hy,decide_true,Bool.true_and]
          cases hrmy:rm.testBit (sd.invBm.getD y 0) with
          | false => simp
          | true =>
            have h1:=((hinv y hy).2 j).2; rw [hst] at h1
            have h2:=hevu (sd.invBm.getD y 0) (hbij y hy).2.1 hrmy
            simp only [sStatVal] at h1
            rw [<- h1,hcp] at h2
            rw [<- h2]; rfl
        · simp [hy]
      | true =>
        right; apply Nat.eq_of_testBit_eq; intro y
        simp only [Nat.testBit_and,hact_tb]
        by_cases hy:y < 1 <<< n
        · simp only [hy,decide_true,Bool.true_and]
          cases hrmy:rm.testBit (sd.invBm.getD y 0) with
          | false => simp
          | true =>
            have h1:=((hinv y hy).2 j).2; rw [hst] at h1
            have h2:=hevu (sd.invBm.getD y 0) (hbij y hy).2.1 hrmy
            simp only [sStatVal] at h1
            rw [<- h1,hcp] at h2
            rw [<- h2]; rfl
        · simp [hy]
    | inr pair =>
      obtain ⟨j',p'⟩:=pair
      have hj':j' < n + res.2.length:=by
        have:=((hinv 0 (by simp [Nat.shiftLeft_eq])).2 j).1; rwa [hst] at this
      refine Or.inr ⟨j',hj',xor p' pol,fun y hy hrmy => ?_⟩
      rw [hact_tb] at hrmy ⊢
      simp only [hy,decide_true,Bool.true_and] at hrmy ⊢
      have h1:=((hinv y hy).2 j).2; rw [hst] at h1
      simp only [sStatVal] at h1
      have h2:=hevu (sd.invBm.getD y 0) (hbij y hy).2.1 hrmy
      rw [<- h2,<- h1]
      cases ((sWiresFrom res.2 (List.ofFn (pt n y))).getD j' false) <;> cases p' <;> cases pol <;> rfl
structure CertNode where
  ws:List ℕ
  paid:List (ℕ × ℕ)
  prune:List ℕ
  edges:List (ℕ × ℕ × ℕ)
  zs:List ℕ
deriving Repr
def paidOf (d:ℕ) (L:List (ℕ × ℕ)) (ri:ℕ):ℕ :=
  match L.find? (fun p => p.1 == ri) with
  | some p => min d p.2
  | none   => d
theorem paidOf_le (d:ℕ) (L:List (ℕ × ℕ)) (ri:ℕ):paidOf d L ri ≤ d:=by
  unfold paidOf
  cases L.find? (fun p => p.1 == ri) with
  | none => exact le_refl _
  | some p => exact Nat.min_le_left _ _
def findEdge (edges:List (ℕ × ℕ × ℕ)) (mc:ℕ):Option (ℕ × ℕ) :=
  match edges.find? (fun e => e.1 == mc) with
  | some e => some e.2
  | none   => none
def mkCandIdx (ws:List ℕ) (i j z kc:ℕ):List ℕ :=
  let a:=ws.getD i 0
  let b:=ws.getD j 0
  mkCand ws a b z kc
def checkEdge (d:ℕ) (slices:BT SliceData) (syms:BT SymData)
    (nextLv:BT CertNode) (u:CertNode) (cw:List ℕ) (z:ℕ) (mc:ℕ):Bool :=
  match findEdge u.edges mc with
  | none => false
  | some (si,ci) =>
    match btGet syms si,btGet nextLv ci with
    | some sd,some child =>
      let mapped:=cw.map (actSwaps sd.swaps)
      (mapped.length == child.ws.length) &&
      (mapped.all fun w => child.ws.contains w) &&
      (child.paid.all fun p =>
        match btGet sd.invSlice p.1 with
        | some ri =>
          match btGet slices ri with
          | some sl =>
            let pr:=projSl sl z
            let zA:=if pr != 0 && !sl.base.contains pr then 1 else 0
            paidOf d u.paid ri + zA ≤ p.2
          | none => false
        | none => false)
    | _,_ => false
def checkCand (full tgt d s nSlices:ℕ) (zs:List ℕ) (slices:BT SliceData) (syms:BT SymData)
    (nextLv:BT CertNode) (u:CertNode) (cw:List ℕ) (z mc:ℕ):Bool :=
  if cw.length > s then true
  else if isUnsep full tgt zs cw then true
  else if u.prune.any (fun ri =>
    if ri < nSlices then
      match btGet slices ri with
      | some sl =>
        let pr:=projSl sl z
        let zA:=if pr != 0 && !sl.base.contains pr then 1 else 0
        let pNew:=paidOf d u.paid ri + zA
        sl.L + countConst sl cw > pNew + (s - 1)
      | none => false
    else false) then true
  else checkEdge d slices syms nextLv u cw z mc
def checkNode (n tgt cap d nSlices:ℕ) (zs:List ℕ) (slices:BT SliceData) (syms:BT SymData)
    (nextLv:BT CertNode) (u:CertNode):Bool :=
  let full:=maskN n
  let s:=cap - d
  let ws:=u.ws
  let len:=ws.length
  (!ws.contains tgt) &&
  ws.Nodup &&
  (ws.all fun w => (w &&& full) == w) &&
  (List.range len).all fun i =>
    (List.range len).all fun j =>
      if j ≤ i then true
      else
        let a:=ws.getD i 0
        let b:=ws.getD j 0
        (List.range 4).all fun op =>
          let z:=applyOp full op a b
          if z == 0 || z == full || ws.contains z then true
          else if z == tgt then false
          else if s ≤ 1 then true
          else
            (List.range 4).all fun kc =>
              let cw:=mkCand ws a b z kc
              let mc:=(((i * 16 + j) * 4 + op) * 4 + kc)
              checkCand full tgt d s nSlices zs slices syms nextLv u cw z mc
theorem nodup_perm_of_length_subset {α:Type} [DecidableEq α] (A B:List α)
    (hndA:A.Nodup) (hndB:B.Nodup) (hlen:A.length = B.length) (hsub:∀ x ∈ A,x ∈ B) :
    A.Perm B:=by
  induction A generalizing B with
  | nil =>
    cases B with
    | nil => exact List.Perm.nil
    | cons _ _ => simp at hlen
  | cons a A ih =>
    obtain ⟨hna,hndA'⟩:=List.nodup_cons.1 hndA
    have haB:a ∈ B:=hsub a List.mem_cons_self
    have hpermB:B.Perm (a :: B.erase a):=List.perm_cons_erase haB
    have hndB':(B.erase a).Nodup:=hndB.erase a
    have hlen':A.length = (B.erase a).length:=by
      have h1:=List.length_erase_of_mem haB
      have h2:1 ≤ B.length:=List.length_pos_of_mem haB
      simp only [List.length_cons] at hlen
      omega
    have hsub':∀ x ∈ A,x ∈ B.erase a:=by
      intro x hx
      have hne:x ≠ a:=fun h => hna (h ▸ hx)
      exact (List.mem_erase_of_ne hne).2 (hsub x (List.mem_cons_of_mem _ hx))
    exact (List.Perm.cons a (ih (B.erase a) hndA' hndB' hlen' hsub')).trans hpermB.symm
theorem checkNode_sound (n tgt cap d nSlices:ℕ) (zs:List ℕ)
    (slices:BT SliceData) (syms:BT SymData)
    (nextLv:BT CertNode) (u:CertNode)
    (hd:d < cap)
    (htgt_mask:tgt &&& maskN n = tgt)
    (hzs:∀ z ∈ zs,z < 1 <<< n /\ tgt.testBit z = false)
    (hslices:∀ (ri:ℕ) (sl:SliceData),btGet slices ri = some sl ->
      sl.rm &&& maskN n = sl.rm /\
      sl.rm &&& sl.low ≠ 0 /\
      projSl sl tgt ≠ 0 /\
      (∀ b' ∈ sl.base,∃ i < n,projSl sl (inpW n i) = b') /\
      (∀ s',HasSignedOn n sl.rm tgt s' -> sl.L ≤ s'))
    (hslices_some:∀ ri < nSlices,∃ sl,btGet slices ri = some sl)
    (hsyms:∀ (si:ℕ) (sd:SymData),btGet syms si = some sd -> symOK n tgt nSlices slices sd = true)
    (hnext:∀ (ci:ℕ) (child:CertNode),btGet nextLv ci = some child ->
      child.ws.Nodup /\
      ((∀ (ri:ℕ) (sl:SliceData),ri < nSlices -> btGet slices ri = some sl ->
        Available n sl.rm child.ws (paidOf (d + 1) child.paid ri)) ->
        ¬ SRun (maskN n) tgt (cap - (d + 1)) child.ws))
    (hok:checkNode n tgt cap d nSlices zs slices syms nextLv u = true)
    (hav:∀ (ri:ℕ) (sl:SliceData),ri < nSlices -> btGet slices ri = some sl ->
      Available n sl.rm u.ws (paidOf d u.paid ri)) :
    ¬ SRun (maskN n) tgt (cap - d) u.ws:=by
  intro hrun
  unfold checkNode at hok
  dsimp only at hok
  simp only [Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true,List.mem_range,
    beq_iff_eq,decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hntgt,hnd_u⟩,hmask_u⟩,hloop⟩:=hok
  have key:∀ s ws',SRun (maskN n) tgt s ws' -> s = cap - d -> ws'.Perm u.ws -> False:=by
    intro s ws' hrun'
    induction hrun' with
    | done s =>
      intro _ hperm
      have ht_in:tgt ∈ u.ws:=hperm.subset List.mem_cons_self
      have:u.ws.contains tgt = true:=List.contains_iff_mem.2 ht_in
      rw [this] at hntgt; cases hntgt
    | perm hperm1 _ ih =>
      intro hs hperm2
      exact ih hs (hperm1.trans hperm2)
    | step s' ws a b op kc hnd_ws ha hb hab hop hkc hz0 hzM hzn hcw_len hsub _ =>
      intro hs hperm
      have hs_eq:s' + 1 = cap - d:=hs
      have ha_u:a ∈ u.ws:=hperm.subset ha
      have hb_u:b ∈ u.ws:=hperm.subset hb
      obtain ⟨ia,hia,ha_eq⟩:=List.getElem_of_mem ha_u
      obtain ⟨ib,hib,hb_eq⟩:=List.getElem_of_mem hb_u
      have hiab:ia ≠ ib:=by intro h; subst h; exact hab (ha_eq.symm.trans hb_eq)
      have horient:∃ i j op' kc',i < u.ws.length /\ j < u.ws.length /\ i < j /\ op' < 4 /\ kc' < 4 /\
          let a':=u.ws.getD i 0
          let b':=u.ws.getD j 0
          let z':=applyOp (maskN n) op' a' b'
          z' = applyOp (maskN n) op a b /\
          (mkCand u.ws a' b' z' kc').Perm (mkCand ws a b (applyOp (maskN n) op a b) kc):=by
        have hperm_cand:(mkCand u.ws a b (applyOp (maskN n) op a b) kc).Perm
            (mkCand ws a b (applyOp (maskN n) op a b) kc):=by
          have hp1:(u.ws.erase a).Perm (ws.erase a):=hperm.symm.erase a
          have hp2:((u.ws.erase a).erase b).Perm ((ws.erase a).erase b):=hp1.erase b
          have hp3:=hp2.append_right [applyOp (maskN n) op a b]
          rcases kc with _ | _ | _ | kc
          · exact hp3
          · exact hp3.append_right [a]
          · exact hp3.append_right [b]
          · exact hp3.append_right [a,b]
        rcases lt_or_gt_of_ne hiab with hlt | hgt
        · refine ⟨ia,ib,op,kc,hia,hib,hlt,hop,hkc,?_,?_⟩
          · simp [List.getD_eq_getElem?_getD,hia,hib,ha_eq,hb_eq]
          · simpa [List.getD_eq_getElem?_getD,hia,hib,ha_eq,hb_eq] using hperm_cand
        · set op':=match op with | 2 => 3 | 3 => 2 | _ => op
          set kc':=match kc with | 1 => 2 | 2 => 1 | _ => kc
          have hswap_op:applyOp (maskN n) op' b a = applyOp (maskN n) op a b:=by
            rcases op with _ | _ | _ | _ | op
            · simp [op',applyOp,Nat.and_comm]
            · simp [op',applyOp,Nat.or_comm]
            · simp [op',applyOp,Nat.and_comm]
            · simp [op',applyOp,Nat.and_comm]
            · omega
          refine ⟨ib,ia,op',kc',hib,hia,hgt,
            by rcases op with _ | _ | _ | _ | op <;> simp [op'] at hop ⊢ <;> omega,
            by rcases kc with _ | _ | _ | _ | kc <;> simp [kc'] at hkc ⊢ <;> omega,?_,?_⟩
          · simp only [List.getD_eq_getElem?_getD,hia,hib,List.getElem?_eq_getElem,Option.getD_some,ha_eq,hb_eq]
            exact hswap_op
          · simp only [List.getD_eq_getElem?_getD,hia,hib,List.getElem?_eq_getElem,Option.getD_some,ha_eq,hb_eq]
            rw [hswap_op]
            exact (mkCand_swap hab).trans hperm_cand
      obtain ⟨i,j,op',kc',hi,hj,hij,hop',hkc',hz_eq,hcw_perm⟩:=horient
      set a':=u.ws.getD i 0
      set b':=u.ws.getD j 0
      set z:=applyOp (maskN n) op' a' b'
      set cw:=mkCand u.ws a' b' z kc'
      have hbody:=hloop i hi j hj
      have hnle:¬ (j ≤ i):=by omega
      simp only [hnle,↓reduceIte,List.all_eq_true,List.mem_range] at hbody
      have hop_ok:=hbody op' hop'
      have hz0':z ≠ 0:=by rw [hz_eq]; exact hz0
      have hzM':z ≠ maskN n:=by rw [hz_eq]; exact hzM
      have hzn':z ∉ u.ws:=by rw [hz_eq]; intro hm; exact hzn (hperm.symm.subset hm)
      have hzn_b:u.ws.contains z = false:=by
        cases h:u.ws.contains z
        · rfl
        · exfalso; exact hzn' (List.contains_iff_mem.1 h)
      have hskip_false:(z == 0 || z == maskN n || u.ws.contains z) = false:=by
        simp only [Bool.or_eq_false_iff,beq_eq_false_iff_ne]
        exact ⟨⟨hz0',hzM'⟩,hzn_b⟩
      simp only [show applyOp (maskN n) op' (u.ws.getD i 0) (u.ws.getD j 0) = z from rfl,
        hskip_false,Bool.false_eq_true,↓reduceIte] at hop_ok
      have hztgt:z ≠ tgt:=by
        intro heq; simp [heq] at hop_ok
      simp only [beq_iff_eq,hztgt,↓reduceIte] at hop_ok
      have hsub_cw:SRun (maskN n) tgt s' cw:=SRun.perm hcw_perm.symm hsub
      by_cases hs1:cap - d ≤ 1
      · have hs'0:s' = 0:=by omega
        subst hs'0
        have htgt_in_cw:∀ wL,SRun (maskN n) tgt 0 wL -> tgt ∈ wL:=by
          intro wL h0
          generalize hzero:0 = s0 at h0
          induction h0 with
          | done _ => exact List.mem_cons_self
          | perm hp _ ih0 => exact hp.subset (ih0 hzero)
          | step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => cases hzero
        have ht_in:tgt ∈ cw:=htgt_in_cw cw hsub_cw
        have ha'_in:a' ∈ u.ws:=by
          simp only [a',List.getD_eq_getElem?_getD,hi,List.getElem?_eq_getElem,Option.getD_some]
          exact List.getElem_mem hi
        have hb'_in:b' ∈ u.ws:=by
          simp only [b',List.getD_eq_getElem?_getD,hj,List.getElem?_eq_getElem,Option.getD_some]
          exact List.getElem_mem hj
        rcases mkCand_subset ha'_in hb'_in tgt ht_in with rfl | ht_u
        · exact hztgt rfl
        · have:u.ws.contains tgt = true:=List.contains_iff_mem.2 ht_u; rw [this] at hntgt; cases hntgt
      · simp only [hs1,↓reduceIte,List.all_eq_true,List.mem_range] at hop_ok
        have hcand:checkCand (maskN n) tgt d (cap - d) nSlices zs slices syms nextLv u cw z (((i * 16 + j) * 4 + op') * 4 + kc') = true :=
          hop_ok kc' hkc'
        unfold checkCand at hcand
        have hcw_le:¬ (cw.length > cap - d):=by
          rw [hcw_perm.length_eq]; omega
        simp only [hcw_le,↓reduceIte] at hcand
        by_cases hun:isUnsep (maskN n) tgt zs cw = true
        · exact isUnsep_sound n tgt zs htgt_mask hzs s' cw hun hsub_cw
        · simp only [hun,Bool.false_eq_true,↓reduceIte] at hcand
          have ha'_in:a' ∈ u.ws:=by
            simp only [a',List.getD_eq_getElem?_getD,hi,List.getElem?_eq_getElem,Option.getD_some]
            exact List.getElem_mem hi
          have hb'_in:b' ∈ u.ws:=by
            simp only [b',List.getD_eq_getElem?_getD,hj,List.getElem?_eq_getElem,Option.getD_some]
            exact List.getElem_mem hj
          have hab':a' ≠ b':=by
            simp only [a',b',List.getD_eq_getElem?_getD,hi,hj,List.getElem?_eq_getElem,Option.getD_some]
            intro heq; have:=(List.Nodup.getElem_inj_iff hnd_u).1 heq; omega
          by_cases hpr:u.prune.any (fun ri =>
              if ri < nSlices then
                match btGet slices ri with
                | some sl =>
                  let pr:=projSl sl z
                  let zA:=if pr != 0 && !sl.base.contains pr then 1 else 0
                  let pNew:=paidOf d u.paid ri + zA
                  sl.L + countConst sl cw > pNew + (cap - d - 1)
                | none => false
              else false) = true
          · simp only [List.any_eq_true] at hpr
            obtain ⟨ri,_,hri_ok⟩:=hpr
            by_cases hri:ri < nSlices
            · simp only [hri,↓reduceIte] at hri_ok
              cases hsl:btGet slices ri with
              | none => simp [hsl] at hri_ok
              | some sl =>
                simp only [hsl,decide_eq_true_eq] at hri_ok
                obtain ⟨hrm,hlow,hnc_t,hbase,hlb⟩:=hslices ri sl hsl
                have hav_cw:=available_step_slice n op' a' b' kc' (paidOf d u.paid ri) sl u.ws
                  hrm hlow hbase ha'_in hb'_in (hav ri sl hri hsl)
                obtain ⟨r,hr,hsig⟩:=srun_available_sound n tgt sl hrm hlow hnc_t s' cw hsub_cw _ hav_cw
                have hLr:sl.L ≤ r:=hlb r hsig
                have hs'_eq:s' = cap - d - 1:=by omega
                rw [hs'_eq] at hr
                change r + countConst sl cw ≤
                  paidOf d u.paid ri + (if projSl sl z != 0 && !sl.base.contains (projSl sl z) then 1 else 0) + (cap - d - 1) at hr
                change sl.L + countConst sl cw >
                  paidOf d u.paid ri + (if projSl sl z != 0 && !sl.base.contains (projSl sl z) then 1 else 0) + (cap - d - 1) at hri_ok
                omega
            · simp [hri] at hri_ok
          ·
            simp only [hpr,Bool.false_eq_true,↓reduceIte] at hcand
            unfold checkEdge at hcand
            cases hfe:findEdge u.edges (((i * 16 + j) * 4 + op') * 4 + kc') with
            | none => simp [hfe] at hcand
            | some ec =>
              obtain ⟨si,ci⟩:=ec
              simp only [hfe] at hcand
              cases hsd:btGet syms si with
              | none => simp [hsd] at hcand
              | some sd =>
                cases hch:btGet nextLv ci with
                | none => simp [hsd,hch] at hcand
                | some child =>
                  simp only [hsd,hch,Bool.and_eq_true,beq_iff_eq,List.all_eq_true] at hcand
                  obtain ⟨⟨hlen_m,hsub_m⟩,hpaid_m⟩:=hcand
                  have hsym_ok:=hsyms si sd hsd
                  unfold symOK at hsym_ok
                  dsimp only at hsym_ok
                  simp only [Bool.and_eq_true,beq_iff_eq,List.all_eq_true,List.mem_range,decide_eq_true_eq] at hsym_ok
                  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_,_⟩,_⟩,_⟩,hbm0_raw⟩,hbij_raw⟩,hvp_raw⟩,hbit_raw⟩,htgt_sw⟩,hsl_sym⟩:=hsym_ok
                  have hbm0:sd.bm.getD 0 0 = 0:=by
                    simp only [Array.getD] at hbm0_raw ⊢
                    split_ifs at hbm0_raw ⊢
                    exact hbm0_raw
                  have hbij:∀ x < 1 <<< n,
                      sd.bm.getD x 0 < 1 <<< n /\ sd.invBm.getD x 0 < 1 <<< n /\
                      sd.invBm.getD (sd.bm.getD x 0) 0 = x /\ sd.bm.getD (sd.invBm.getD x 0) 0 = x:=by
                    intro x hx
                    have h:=hbij_raw x hx
                    exact ⟨h.1.1.1.1,h.1.1.1.2,h.1.1.2,h.1.2⟩
                  have hbasis:∀ x < 1 <<< n,actSwaps sd.swaps (1 <<< x) = 1 <<< sd.bm.getD x 0 :=
                    fun x hx => (hbij_raw x hx).2
                  have hsw_eq:∀ w,w &&& maskN n = w -> actSwaps sd.swaps w = actW (1 <<< n) sd.bm w :=
                    fun w hw => actSwaps_eq_actW n sd.bm sd.swaps hbasis w hw
                  have htgt_sym:actW (1 <<< n) sd.bm tgt = tgt:=by
                    rw [<- hsw_eq tgt htgt_mask]; exact htgt_sw
                  have hvp_lt:∀ v < n,sd.vp.getD v 0 < n:=fun v hv => (hvp_raw v hv).1.1.1
                  have hcw_mask:∀ w ∈ cw,w &&& maskN n = w:=by
                    intro w hw
                    rcases mkCand_subset ha'_in hb'_in w hw with rfl | hw'
                    · have hma:=hmask_u a' ha'_in; have hmb:=hmask_u b' hb'_in
                      rcases op' with _ | _ | _ | op' <;>
                      · apply normW_le_mask; apply Nat.eq_of_testBit_eq; intro k
                        have hka:=congrArg (fun x => x.testBit k) hma
                        have hkb:=congrArg (fun x => x.testBit k) hmb
                        simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor] at hka hkb ⊢
                        cases hmk':(maskN n).testBit k <;> simp [hmk'] at hka hkb ⊢ <;> simp [hka,hkb]
                    · exact hmask_u w hw'
                  have hmap_sw_eq:cw.map (actSwaps sd.swaps) = cw.map (actW (1 <<< n) sd.bm) :=
                    List.map_congr_left (fun w hw => hsw_eq w (hcw_mask w hw))
                  rw [hmap_sw_eq] at hlen_m hsub_m
                  have hnd_cw:cw.Nodup:=mkCand_nodup hnd_u ha'_in hb'_in hab' hzn'
                  obtain ⟨_,_,hactInj,_⟩:=actW_comm_ops n sd hbij hbm0
                  have hnd_mapped:(cw.map (actW (1 <<< n) sd.bm)).Nodup:=by
                    apply List.Nodup.map_on _ hnd_cw
                    intro x hx y hy heq; exact hactInj x y heq (hcw_mask x hx) (hcw_mask y hy)
                  obtain ⟨hnd_child,hchild_invalid⟩:=hnext ci child hch
                  have hperm_child:(cw.map (actW (1 <<< n) sd.bm)).Perm child.ws :=
                    nodup_perm_of_length_subset _ _ hnd_mapped hnd_child hlen_m
                      (fun w hw => List.mem_of_elem_eq_true (hsub_m w hw))
                  have hrun_child:SRun (maskN n) tgt (cap - (d + 1)) child.ws:=by
                    have h1:=SRun.perm hperm_child (srun_actW n tgt sd hbij hbm0 htgt_sym s' cw hcw_mask hsub_cw)
                    have hs'_eq:s' = cap - (d + 1):=by omega
                    rwa [hs'_eq] at h1
                  apply hchild_invalid _ hrun_child
                  intro dri slD hdri hslD
                  have hsl_ok:=hsl_sym dri hdri
                  cases hisl:btGet sd.invSlice dri with
                  | none => simp [hisl] at hsl_ok
                  | some ri =>
                    simp only [hisl,hslD] at hsl_ok
                    cases hslR:btGet slices ri with
                    | none => simp [hslR] at hsl_ok
                    | some slR =>
                      simp only [hslR,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at hsl_ok
                      obtain ⟨hri_lt,hrm_sw⟩:=hsl_ok
                      obtain ⟨hrm_ri,hlow_ri,_,hbase_ri,_⟩:=hslices ri slR hslR
                      have hrm_eq:actW (1 <<< n) sd.bm slR.rm = slD.rm:=by
                        rw [<- hsw_eq slR.rm hrm_ri]; exact hrm_sw
                      have hav_cw_ri:=available_step_slice n op' a' b' kc' (paidOf d u.paid ri) slR u.ws
                        hrm_ri hlow_ri hbase_ri ha'_in hb'_in (hav ri slR hri_lt hslR)
                      have hav_map_dri:=available_actW n slR.rm _ sd cw hbij hvp_lt hbit_raw hav_cw_ri
                      rw [hrm_eq] at hav_map_dri
                      have hav_child_dri:=available_perm hperm_child hav_map_dri
                      apply available_mono _ hav_child_dri
                      have h1:paidOf d u.paid ri ≤ d:=paidOf_le d u.paid ri
                      have h2:(if projSl slR z != 0 && !slR.base.contains (projSl slR z) then 1 else 0) ≤ 1:=by
                        split_ifs <;> omega
                      change paidOf d u.paid ri + (if projSl slR z != 0 && !slR.base.contains (projSl slR z) then 1 else 0) ≤
                        match child.paid.find? (fun p => p.1 == dri) with
                        | some p => min (d + 1) p.2
                        | none   => d + 1
                      cases hfc:child.paid.find? (fun p => p.1 == dri) with
                      | none => exact Nat.add_le_add h1 h2
                      | some p =>
                        have hpmem:=List.mem_of_find?_eq_some hfc
                        have hpeq:p.1 = dri:=by have h:=List.find?_some hfc; simpa using h
                        have hp_ok:=hpaid_m p hpmem
                        rw [hpeq] at hp_ok
                        simp only [hisl,hslR,decide_eq_true_eq] at hp_ok
                        exact Nat.le_min.2 ⟨Nat.add_le_add h1 h2,by simpa only [Bool.and_eq_true] using hp_ok⟩
  exact key (cap - d) u.ws hrun rfl (List.Perm.refl _)
theorem cert_sound (n tgt cap nSlices:ℕ) (zs:List ℕ)
    (bases:Array (ℕ × ℕ × ℕ))
    (slices:BT SliceData) (syms:BT SymData)
    (levels:Array (BT CertNode))
    (htgt_mask:tgt &&& maskN n = tgt)
    (htgt0:tgt.testBit 0 = false)
    (hnc:∃ z1 o1,z1 < 1 <<< n /\ o1 < 1 <<< n /\ tgt.testBit z1 ≠ tgt.testBit o1)
    (hall_ess:∀ i < n,∃ k1 k2,k1 < 1 <<< n /\ k2 < 1 <<< n /\
      (∀ j < n,j ≠ i -> k1.testBit j = k2.testBit j) /\ tgt.testBit k1 ≠ tgt.testBit k2)
    (hzs:∀ z ∈ zs,z < 1 <<< n /\ tgt.testBit z = false)
    (hbases:∀ i (hi:i < bases.size),
      let (bm,bTgt,bL):=bases[i]
      ∀ s,HasSignedOn bm (maskN bm) bTgt s -> bL ≤ s)
    (hslices_ok:btAll (sliceOK n tgt bases) slices = true)
    (hslices_some:∀ ri < nSlices,∃ sl,btGet slices ri = some sl)
    (hsyms_ok:btAll (symOK n tgt nSlices slices) syms = true)
    (hlevels_len:levels.size = cap)
    (hlevels_ok:∀ (d:ℕ) (hd:d < cap),
      let nextLv:BT CertNode:=if h:d + 1 < levels.size then levels[d + 1] else BT.leaf none
      btAll (checkNode n tgt cap d nSlices zs slices syms nextLv) (levels[d]'(by omega)) = true)
    (hroot:∃ h0:0 < levels.size,∃ r0:CertNode,
      btGet levels[0] 0 = some r0 /\
      r0.ws.Perm ((List.range n).map (inpW n)) /\ r0.paid = []) :
    ¬ HasSignedOn n (maskN n) tgt cap:=by
  have hslices:∀ (ri:ℕ) (sl:SliceData),btGet slices ri = some sl ->
      sl.rm &&& maskN n = sl.rm /\
      sl.rm &&& sl.low ≠ 0 /\
      projSl sl tgt ≠ 0 /\
      (∀ b' ∈ sl.base,∃ i < n,projSl sl (inpW n i) = b') /\
      (∀ s',HasSignedOn n sl.rm tgt s' -> sl.L ≤ s'):=by
    intro ri sl hsl
    have hok:=btAll_sound _ slices hslices_ok ri sl hsl
    have hlb:=sliceOK_sound n tgt bases hbases sl hok
    unfold sliceOK at hok; dsimp only at hok
    simp only [Bool.and_eq_true,beq_iff_eq,bne_iff_ne,ne_eq,List.all_eq_true,List.any_eq_true,
      List.mem_range] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨hrm_eq,hlow⟩,_⟩,_⟩,_⟩,hbase_raw⟩,hzo⟩,_⟩:=hok
    have hrm_mask:sl.rm &&& maskN n = sl.rm:=by
      rw [hrm_eq]; apply Nat.eq_of_testBit_eq; intro k
      simp only [Nat.testBit_and,maskSub,encB_testBit,testBit_maskN]
      cases decide (k < 1 <<< n) <;> simp
    have hnc_t:projSl sl tgt ≠ 0:=by
      intro hz
      have hconst:=(projSl_eq_zero_iff sl hlow tgt).1 hz
      obtain ⟨z1,o1,hz1,ho1,hrmz,hrmo,hne⟩:=hasZeroAndOne_sound n sl.rm tgt hzo
      rcases hconst with h0 | h1
      · have ez:=congrArg (fun x => x.testBit z1) h0
        have eo:=congrArg (fun x => x.testBit o1) h0
        simp [Nat.testBit_and,hrmz,hrmo] at ez eo
        exact hne (ez.trans eo.symm)
      · have ez:=congrArg (fun x => x.testBit z1) h1
        have eo:=congrArg (fun x => x.testBit o1) h1
        simp [Nat.testBit_and,hrmz,hrmo] at ez eo
        exact hne (ez.trans eo.symm)
    refine ⟨hrm_mask,hlow,hnc_t,fun b' hb' => ?_,hlb⟩
    obtain ⟨i,hi,heq⟩:=hbase_raw b' hb'
    exact ⟨i,hi,heq⟩
  have hsyms:∀ (si:ℕ) (sd:SymData),btGet syms si = some sd -> symOK n tgt nSlices slices sd = true :=
    btAll_sound _ syms hsyms_ok
  have hind:∀ r ≤ cap,∀ (hlt:cap - r < cap),
      ∀ (ni:ℕ) (u:CertNode),btGet (levels[cap - r]'(by omega)) ni = some u ->
      let d:=cap - r
      u.ws.Nodup /\
      ((∀ (ri:ℕ) (sl:SliceData),ri < nSlices -> btGet slices ri = some sl ->
        Available n sl.rm u.ws (paidOf d u.paid ri)) ->
        ¬ SRun (maskN n) tgt (cap - d) u.ws):=by
    intro r
    induction r with
    | zero => intro _ hlt; omega
    | succ r ih =>
      intro hr hlt ni u hu
      set d:=cap - (r + 1)
      set nextLv:BT CertNode:=if h:d + 1 < levels.size then levels[d + 1] else BT.leaf none
      have hok:=btAll_sound _ _ (hlevels_ok d hlt) ni u hu
      have hnd_u:u.ws.Nodup:=by
        unfold checkNode at hok; dsimp only at hok
        simp only [Bool.and_eq_true,decide_eq_true_eq] at hok
        exact hok.1.1.2
      refine ⟨hnd_u,fun hav => ?_⟩
      apply checkNode_sound n tgt cap d nSlices zs slices syms nextLv u hlt htgt_mask hzs hslices hslices_some hsyms _ hok hav
      intro ci child hch
      by_cases hd1:d + 1 < cap
      · have hd1_eq:d + 1 = cap - r:=by omega
        have hnxt:nextLv = levels[cap - r]'(by omega):=by
          simp only [nextLv,show d + 1 < levels.size by omega,↓reduceDIte]
          congr 1
        rw [hnxt] at hch
        simpa [hd1_eq] using ih (by omega) (by omega) ci child hch
      · have hnxt:nextLv = BT.leaf none:=by simp [nextLv,show ¬ (d + 1 < levels.size) by omega]
        rw [hnxt] at hch; cases hch
  intro hhas
  have hrun:=srun_of_hasSigned n tgt cap htgt_mask htgt0 hnc hall_ess hhas
  obtain ⟨h0,r0,hr0,hroot_perm,hroot_paid⟩:=hroot
  have hcap_pos:0 < cap:=by omega
  have hzero:=hind cap (le_refl _) (by omega) 0 r0 (by simpa using hr0)
  simp only [Nat.sub_self,Nat.sub_zero] at hzero
  apply hzero.2
  · intro ri sl _ _
    rw [hroot_paid]
    have hpaid0:paidOf 0 [] ri = 0:=rfl
    rw [hpaid0]
    exact available_perm hroot_perm.symm (available_inputs n sl.rm)
  · exact SRun.perm hroot_perm.symm hrun
theorem btAll_mono {α:Type} {p q:α -> Bool} (h:∀ x,p x = true -> q x = true) :
    ∀ t:BT α,btAll p t = true -> btAll q t = true
  | .leaf none,_ => rfl
  | .leaf (some a),ha => h a ha
  | .node l r,hlr => by
    simp only [btAll,Bool.and_eq_true] at hlr ⊢
    exact ⟨btAll_mono h l hlr.1,btAll_mono h r hlr.2⟩
def litW (full k0 w:ℕ):ℕ :=
  if w.testBit k0 then w else w ^^^ full
theorem testBit_eq_land_shiftLeft (w k:ℕ) :
    ((w &&& (1 <<< k)) != 0) = w.testBit k:=by
  cases h:w.testBit k with
  | false =>
    have h0:w &&& (1 <<< k) = 0:=by
      apply Nat.eq_of_testBit_eq; intro j
      simp only [Nat.testBit_and,Nat.zero_testBit]
      by_cases hjk:j = k
      · subst hjk; simp [h]
      · simp [show ¬ (j = k) by omega]
    simp [h0]
  | true =>
    have hne:w &&& (1 <<< k) ≠ 0:=by
      intro h0
      have h1:=congrArg (fun x => x.testBit k) h0
      simp [Nat.testBit_and,h] at h1
    simp [bne_iff_ne,hne]
def normWFast (full r:ℕ):ℕ :=
  if (r &&& 1) != 0 then r ^^^ full else r
theorem normWFast_eq_normW (full r:ℕ):normWFast full r = normW full r:=by
  unfold normWFast normW
  have h:=testBit_eq_land_shiftLeft r 0
  simp only [Nat.shiftLeft_zero] at h
  rw [h]
def sufAnd (full:ℕ):List ℕ -> ℕ × List ℕ
  | [] => (full,[])
  | l :: rest =>
    let p:=sufAnd full rest
    (l &&& p.1,p.1 :: p.2)
theorem sufAnd_fst (full:ℕ):∀ ls:List ℕ,(sufAnd full ls).1 = ls.foldr (· &&& ·) full
  | [] => rfl
  | l :: rest => by simp only [sufAnd,List.foldr_cons,sufAnd_fst full rest]
theorem foldl_and_assoc_init (ls:List ℕ) :
    ∀ a b:ℕ,ls.foldl (· &&& ·) (a &&& b) = a &&& ls.foldl (· &&& ·) b:=by
  induction ls with
  | nil => intro _ _; rfl
  | cons x xs ih =>
    intro a b
    simp only [List.foldl_cons,Nat.and_assoc]
    exact ih a (b &&& x)
theorem foldl_and_perm {l1 l2:List ℕ} (hp:l1.Perm l2) :
    ∀ m:ℕ,l1.foldl (· &&& ·) m = l2.foldl (· &&& ·) m:=by
  induction hp with
  | nil => intro _; rfl
  | cons x _ ih => intro m; simp only [List.foldl_cons]; exact ih _
  | swap x y l =>
    intro m
    simp only [List.foldl_cons]
    congr 1
    rw [Nat.and_assoc,Nat.and_comm y x,<- Nat.and_assoc]
  | trans _ _ ih1 ih2 => intro m; exact (ih1 m).trans (ih2 m)
theorem foldr_and_eq_foldl (full:ℕ) :
    ∀ (ls:List ℕ) (m:ℕ),m &&& full = m -> m &&& ls.foldr (· &&& ·) full = ls.foldl (· &&& ·) m
  | [],m,hm => by simp [hm]
  | a :: rest,m,hm => by
    simp only [List.foldr_cons,List.foldl_cons]
    rw [<- Nat.and_assoc]
    have hma:(m &&& a) &&& full = m &&& a:=by
      rw [Nat.and_assoc,Nat.and_comm a full,<- Nat.and_assoc,hm]
    exact foldr_and_eq_foldl full rest (m &&& a) hma
theorem foldl_and_full_inv (full:ℕ) :
    ∀ (ls:List ℕ) (m:ℕ),m &&& full = m -> ls.foldl (· &&& ·) m &&& full = ls.foldl (· &&& ·) m
  | [],m,hm => hm
  | a :: rest,m,hm => by
    simp only [List.foldl_cons]
    apply foldl_and_full_inv full rest (m &&& a)
    rw [Nat.and_assoc,Nat.and_comm a full,<- Nat.and_assoc,hm]
theorem foldl_unsep_eq_map (full k0:ℕ) :
    ∀ (ws:List ℕ) (m:ℕ),
      ws.foldl (fun acc w => if w.testBit k0 then acc &&& w else acc &&& (w ^^^ full)) m =
      (ws.map (litW full k0)).foldl (· &&& ·) m
  | [],_ => rfl
  | w :: ws,m => by
    simp only [List.foldl_cons,List.map_cons,litW]
    split_ifs <;> exact foldl_unsep_eq_map full k0 ws _
theorem foldl_and_ne_zero_of_cons {a:ℕ} {ls:List ℕ} {m:ℕ}
    (h:(a :: ls).foldl (· &&& ·) m ≠ 0):ls.foldl (· &&& ·) m ≠ 0:=by
  intro hz
  simp only [List.foldl_cons] at h
  rw [Nat.and_comm m a,foldl_and_assoc_init,hz,Nat.and_zero] at h
  exact h rfl
def zUnsepAny (z:ℕ):List (ℕ × ℕ) -> Bool
  | [] => false
  | (bit,m) :: rest =>
    let mz:=m &&& z
    let hit :=
      if mz == 0 then (z &&& bit) == 0
      else if mz == m then (z &&& bit) != 0
      else true
    if hit then true else zUnsepAny z rest
def PairInv (full tgt:ℕ) (zs sub:List ℕ) (p:ℕ × ℕ):Prop :=
  ∃ k0 ∈ zs,p.1 = 1 <<< k0 /\ p.2 ≠ 0 /\ p.2 = (sub.map (litW full k0)).foldl (· &&& ·) tgt
theorem zUnsepAny_sound (full tgt z:ℕ) (zs sub cw:List ℕ)
    (htgt_mask:tgt &&& full = tgt)
    (hperm:cw.Perm (z :: sub))
    (pairs:List (ℕ × ℕ))
    (hinv:∀ p ∈ pairs,PairInv full tgt zs sub p)
    (hres:zUnsepAny z pairs = true) :
    isUnsep full tgt zs cw = true:=by
  induction pairs with
  | nil => simp [zUnsepAny] at hres
  | cons p rest ih =>
    obtain ⟨bit,m⟩:=p
    simp only [zUnsepAny] at hres
    cases hhit:(if (m &&& z) == 0 then (z &&& bit) == 0 else if (m &&& z) == m then (z &&& bit) != 0 else true) with
    | false =>
      simp only [hhit,Bool.false_eq_true,↓reduceIte] at hres
      exact ih (fun q hq => hinv q (List.mem_cons_of_mem _ hq)) hres
    | true =>
      obtain ⟨k0,hk0_zs,hbit,hm_ne,hm_eq⟩:=hinv (bit,m) List.mem_cons_self
      dsimp only at hbit hm_ne hm_eq
      have hm_full:m &&& full = m:=by
        rw [hm_eq]; exact foldl_and_full_inv full _ tgt htgt_mask
      have hmlit_ne:m &&& litW full k0 z ≠ 0:=by
        have htb:=testBit_eq_land_shiftLeft z k0
        rw [<- hbit] at htb
        by_cases hmz0:m &&& z = 0
        · simp only [hmz0,beq_self_eq_true,↓reduceIte,beq_iff_eq] at hhit
          have hz0:z.testBit k0 = false:=by rw [<- htb]; simp [hhit]
          simp only [litW,hz0,Bool.false_eq_true,↓reduceIte]
          have:m &&& (z ^^^ full) = m:=by
            apply Nat.eq_of_testBit_eq; intro k
            have hmf:=congrArg (fun x => x.testBit k) hm_full
            have h0:=congrArg (fun x => x.testBit k) hmz0
            simp only [Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at hmf h0 ⊢
            cases hmk:m.testBit k with
            | false => simp
            | true =>
              simp only [hmk,Bool.true_and] at hmf h0
              simp [hmf,h0]
          rw [this]; exact hm_ne
        · by_cases hmzm:m &&& z = m
          · simp only [hmzm,show (m == 0) = false by simp [hm_ne],
              beq_self_eq_true,Bool.false_eq_true,↓reduceIte] at hhit
            have hz1:z.testBit k0 = true:=by rw [<- htb]; exact hhit
            simp only [litW,hz1,↓reduceIte,hmzm]
            exact hm_ne
          · simp only [litW]
            cases z.testBit k0 with
            | true => exact hmz0
            | false =>
              intro heq0
              apply hmzm
              apply Nat.eq_of_testBit_eq; intro k
              have hmf:=congrArg (fun x => x.testBit k) hm_full
              have h0:=congrArg (fun x => x.testBit k) heq0
              simp only [Bool.false_eq_true,↓reduceIte,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at hmf h0 ⊢
              cases hmk:m.testBit k with
              | false => simp
              | true =>
                simp only [hmk,Bool.true_and] at hmf h0
                rw [hmf] at h0
                cases hzk:z.testBit k with
                | true => rfl
                | false => simp [hzk] at h0
      unfold isUnsep
      rw [List.any_eq_true]
      refine ⟨k0,hk0_zs,?_⟩
      rw [isUnsepOne_eq_foldl,foldl_unsep_eq_map,foldl_and_perm (hperm.map _)]
      simp only [List.map_cons,List.foldl_cons,bne_iff_ne,ne_eq]
      rw [Nat.and_comm tgt (litW full k0 z),foldl_and_assoc_init,<- hm_eq,Nat.and_comm]
      exact hmlit_ne
def ZInv (full tgt:ℕ) (zs pre post:List ℕ) (st:ℕ × ℕ × List ℕ × List ℕ):Prop :=
  ∃ k0 ∈ zs,
    st.1 = 1 <<< k0 /\
    st.2.1 = (pre.map (litW full k0)).foldl (· &&& ·) tgt /\
    st.2.2.1 = post.map (litW full k0) /\
    st.2.2.2 = (sufAnd full st.2.2.1).2
def buildDrop1:List (ℕ × ℕ × List ℕ × List ℕ) -> ℕ -> List (List (ℕ × ℕ))
  | _,0 => []
  | states,k + 1 =>
    let d1:=states.filterMap fun st =>
      match st.2.2.2 with
      | s :: _ => let m:=st.2.1 &&& s; if m == 0 then none else some (st.1,m)
      | [] => none
    let nextStates:=states.filterMap fun st =>
      match st.2.2.1,st.2.2.2 with
      | l :: lt,_ :: stail =>
        let m:=st.2.1 &&& l
        if m == 0 then none else some (st.1,m,lt,stail)
      | _,_ => none
    d1 :: buildDrop1 nextStates k
theorem extract_d_inv (full tgt:ℕ) (zs pre:List ℕ) (x:ℕ) (post:List ℕ)
    (htgt_mask:tgt &&& full = tgt)
    (states:List (ℕ × ℕ × List ℕ × List ℕ))
    (hinv:∀ st ∈ states,ZInv full tgt zs pre (x :: post) st) :
    ∀ p ∈ states.filterMap (fun st =>
      match st.2.2.2 with
      | s :: _ => let m:=st.2.1 &&& s; if m == 0 then none else some (st.1,m)
      | [] => none),PairInv full tgt zs (pre ++ post) p:=by
  intro p hp
  rw [List.mem_filterMap] at hp
  obtain ⟨st,hst_mem,hst_eq⟩:=hp
  obtain ⟨k0,hk0,hbit,hpref,hls,hss⟩:=hinv st hst_mem
  have hss':st.2.2.2 = (post.map (litW full k0)).foldr (· &&& ·) full :: (sufAnd full (post.map (litW full k0))).2:=by
    rw [hss,hls]; simp only [List.map_cons,sufAnd,sufAnd_fst]
  rw [hss'] at hst_eq
  dsimp only at hst_eq
  by_cases hm0:st.2.1 &&& (post.map (litW full k0)).foldr (· &&& ·) full = 0
  · simp [hm0] at hst_eq
  · simp only [show ((st.2.1 &&& (post.map (litW full k0)).foldr (· &&& ·) full) == 0) = false by simp [hm0],
      Bool.false_eq_true,↓reduceIte,Option.some.injEq] at hst_eq
    subst hst_eq
    refine ⟨k0,hk0,hbit,hm0,?_⟩
    rw [hpref,List.map_append,List.foldl_append]
    exact foldr_and_eq_foldl full (post.map (litW full k0)) _ (foldl_and_full_inv full _ tgt htgt_mask)
theorem step_states_inv (full tgt:ℕ) (zs pre:List ℕ) (x:ℕ) (post:List ℕ)
    (states:List (ℕ × ℕ × List ℕ × List ℕ))
    (hinv:∀ st ∈ states,ZInv full tgt zs pre (x :: post) st) :
    ∀ st' ∈ states.filterMap (fun st =>
      match st.2.2.1,st.2.2.2 with
      | l :: lt,_ :: stail =>
        let m:=st.2.1 &&& l
        if m == 0 then none else some (st.1,m,lt,stail)
      | _,_ => none),ZInv full tgt zs (pre ++ [x]) post st':=by
  intro st' hmem
  rw [List.mem_filterMap] at hmem
  obtain ⟨st,hst_mem,hst_eq⟩:=hmem
  obtain ⟨k0,hk0,hbit,hpref,hls,hss⟩:=hinv st hst_mem
  have hls':st.2.2.1 = litW full k0 x :: post.map (litW full k0):=by
    rw [hls]; rfl
  have hss':st.2.2.2 = (sufAnd full (post.map (litW full k0))).1 :: (sufAnd full (post.map (litW full k0))).2:=by
    rw [hss,hls']; rfl
  rw [hls',hss'] at hst_eq
  dsimp only at hst_eq
  by_cases hm0:st.2.1 &&& litW full k0 x = 0
  · simp [hm0] at hst_eq
  · simp only [show ((st.2.1 &&& litW full k0 x) == 0) = false by simp [hm0],
      Bool.false_eq_true,↓reduceIte,Option.some.injEq] at hst_eq
    subst hst_eq
    refine ⟨k0,hk0,hbit,?_,rfl,rfl⟩
    simp only [List.map_append,List.map_cons,List.map_nil,List.foldl_append,List.foldl_cons,List.foldl_nil,hpref]
theorem skip_states_inv (full tgt:ℕ) (zs pre:List ℕ) (x:ℕ) (post:List ℕ)
    (states:List (ℕ × ℕ × List ℕ × List ℕ))
    (hinv:∀ st ∈ states,ZInv full tgt zs pre (x :: post) st) :
    ∀ st' ∈ states.filterMap (fun st =>
      match st.2.2.1,st.2.2.2 with
      | _ :: lt,_ :: stail => some (st.1,st.2.1,lt,stail)
      | _,_ => none),ZInv full tgt zs pre post st':=by
  intro st' hmem
  rw [List.mem_filterMap] at hmem
  obtain ⟨st,hst_mem,hst_eq⟩:=hmem
  obtain ⟨k0,hk0,hbit,hpref,hls,hss⟩:=hinv st hst_mem
  have hls':st.2.2.1 = litW full k0 x :: post.map (litW full k0):=by
    rw [hls]; rfl
  have hss':st.2.2.2 = (sufAnd full (post.map (litW full k0))).1 :: (sufAnd full (post.map (litW full k0))).2:=by
    rw [hss,hls']; rfl
  rw [hls',hss'] at hst_eq
  simp only [Option.some.injEq] at hst_eq
  subst hst_eq
  exact ⟨k0,hk0,hbit,hpref,rfl,rfl⟩
def D1Inv (full tgt:ℕ) (zs:List ℕ):List ℕ -> List ℕ -> List (List (ℕ × ℕ)) -> Prop
  | _,[],_ => True
  | pre,x :: post,d1All =>
    (match d1All with | h :: _ => ∀ p ∈ h,PairInv full tgt zs (pre ++ post) p | [] => True) /\
    D1Inv full tgt zs (pre ++ [x]) post (match d1All with | _ :: t => t | [] => [])
theorem buildDrop1_inv (full tgt:ℕ) (zs:List ℕ) (htgt_mask:tgt &&& full = tgt) :
    ∀ (post pre:List ℕ) (states:List (ℕ × ℕ × List ℕ × List ℕ)),
      (∀ st ∈ states,ZInv full tgt zs pre post st) ->
      D1Inv full tgt zs pre post (buildDrop1 states post.length)
  | [],_,_,_ => trivial
  | x :: post,pre,states,hinv => by
    simp only [List.length_cons,buildDrop1,D1Inv]
    refine ⟨extract_d_inv full tgt zs pre x post htgt_mask states hinv,?_⟩
    exact buildDrop1_inv full tgt zs htgt_mask post (pre ++ [x]) _ (step_states_inv full tgt zs pre x post states hinv)
theorem d1Inv_nil (full tgt:ℕ) (zs:List ℕ):∀ pre post,D1Inv full tgt zs pre post []
  | _,[] => trivial
  | pre,x :: post => ⟨trivial,d1Inv_nil full tgt zs (pre ++ [x]) post⟩
def checkPruneFast (s:ℕ) (pruneInfo:List (SliceData × ℕ × ℕ × List Bool))
    (z:ℕ) (i j:ℕ) (dropA dropB:Bool):Bool :=
  pruneInfo.any fun (sl,pOld,ccAll,cFlags) =>
    let pr:=projSl sl z
    let zA:=if pr != 0 && !sl.base.contains pr then 1 else 0
    let cZ:=if pr == 0 then 1 else 0
    let dA:=if dropA && cFlags.getD i false then 1 else 0
    let dB:=if dropB && cFlags.getD j false then 1 else 0
    sl.L + (ccAll - dA - dB + cZ) > pOld + zA + (s - 1)
theorem countConst_eq_filter_map (sl:SliceData) (ws:List ℕ) :
    countConst sl ws = ((ws.map fun w => projSl sl w == 0).filter id).length:=by
  unfold countConst
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.filter_cons,List.map_cons]
    cases projSl sl w == 0 <;> simp [ih]
theorem countConst_mkCand (sl:SliceData) (ws:List ℕ) (hnd:ws.Nodup)
    (i j:ℕ) (hij:i < j) (hj:j < ws.length) (z:ℕ) :
    let a:=ws.getD i 0
    let b:=ws.getD j 0
    let cA:=if projSl sl a == 0 then 1 else 0
    let cB:=if projSl sl b == 0 then 1 else 0
    let cZ:=if projSl sl z == 0 then 1 else 0
    (countConst sl (mkCand ws a b z 0) = countConst sl ws - cA - cB + cZ) /\
    (countConst sl (mkCand ws a b z 1) = countConst sl ws - cB + cZ) /\
    (countConst sl (mkCand ws a b z 2) = countConst sl ws - cA + cZ) /\
    (countConst sl (mkCand ws a b z 3) = countConst sl ws + cZ):=by
  intro a b cA cB cZ
  have hi:i < ws.length:=by omega
  have ha_eq:a = ws[i]:=by simp [a,List.getD_eq_getElem?_getD,hi]
  have hb_eq:b = ws[j]:=by simp [b,List.getD_eq_getElem?_getD,hj]
  have ha_mem:a ∈ ws:=by rw [ha_eq]; exact List.getElem_mem hi
  have hb_mem:b ∈ ws:=by rw [hb_eq]; exact List.getElem_mem hj
  have hab:a ≠ b:=by
    rw [ha_eq,hb_eq]
    intro heq
    have:=(List.Nodup.getElem_inj_iff hnd).1 heq
    omega
  have hb_mem':b ∈ ws.erase a:=(List.mem_erase_of_ne hab.symm).2 hb_mem
  set rem:=(ws.erase a).erase b
  have hperm_ws:ws.Perm (a :: b :: rem) :=
    (List.perm_cons_erase ha_mem).trans (List.Perm.cons a (List.perm_cons_erase hb_mem'))
  have hcc_ws:countConst sl ws = cA + cB + countConst sl rem:=by
    rw [countConst_perm sl hperm_ws]
    simp only [countConst,List.filter_cons,cA,cB]
    cases projSl sl a == 0 <;> cases projSl sl b == 0 <;> simp <;> omega
  have hcc_base:countConst sl (rem ++ [z]) = countConst sl rem + cZ:=by
    simp only [countConst,List.filter_append,List.filter_cons,List.filter_nil,List.length_append,List.length_nil,cZ]
    cases projSl sl z == 0 <;> simp
  refine ⟨?_,?_,?_,?_⟩
  · simp only [mkCand,rem] at *; rw [hcc_base,hcc_ws]; omega
  · simp only [mkCand,rem] at *
    have:countConst sl ((rem ++ [z]) ++ [a]) = countConst sl (rem ++ [z]) + cA:=by
      simp only [countConst,List.filter_append,List.filter_cons,List.filter_nil,List.length_append,List.length_nil,cA]
      cases projSl sl a == 0 <;> simp
    rw [this,hcc_base,hcc_ws]; omega
  · simp only [mkCand,rem] at *
    have:countConst sl ((rem ++ [z]) ++ [b]) = countConst sl (rem ++ [z]) + cB:=by
      simp only [countConst,List.filter_append,List.filter_cons,List.filter_nil,List.length_append,List.length_nil,cB]
      cases projSl sl b == 0 <;> simp
    rw [this,hcc_base,hcc_ws]; omega
  · simp only [mkCand,rem] at *
    have:countConst sl ((rem ++ [z]) ++ [a,b]) = countConst sl (rem ++ [z]) + cA + cB:=by
      simp only [countConst,List.filter_append,List.filter_cons,List.filter_nil,List.length_append,List.length_nil,cA,cB]
      cases projSl sl a == 0 <;> cases projSl sl b == 0 <;> simp <;> omega
    rw [this,hcc_base,hcc_ws]; omega
theorem mkCand_lengths (ws:List ℕ) (hnd:ws.Nodup) (i j:ℕ) (hij:i < j) (hj:j < ws.length) (z:ℕ) :
    let a:=ws.getD i 0
    let b:=ws.getD j 0
    (mkCand ws a b z 0).length = ws.length - 1 /\
    (mkCand ws a b z 1).length = ws.length /\
    (mkCand ws a b z 2).length = ws.length /\
    (mkCand ws a b z 3).length = ws.length + 1:=by
  intro a b
  have hi:i < ws.length:=by omega
  have ha_eq:a = ws[i]:=by simp [a,List.getD_eq_getElem?_getD,hi]
  have hb_eq:b = ws[j]:=by simp [b,List.getD_eq_getElem?_getD,hj]
  have ha_mem:a ∈ ws:=by rw [ha_eq]; exact List.getElem_mem hi
  have hb_mem:b ∈ ws:=by rw [hb_eq]; exact List.getElem_mem hj
  have hab:a ≠ b:=by
    rw [ha_eq,hb_eq]
    intro heq
    have:=(List.Nodup.getElem_inj_iff hnd).1 heq
    omega
  have hb_mem':b ∈ ws.erase a:=(List.mem_erase_of_ne hab.symm).2 hb_mem
  have h1:(ws.erase a).length = ws.length - 1:=List.length_erase_of_mem ha_mem
  have h2:((ws.erase a).erase b).length = (ws.erase a).length - 1:=List.length_erase_of_mem hb_mem'
  simp only [mkCand,List.length_append,List.length_cons,List.length_nil]
  omega
def checkOneOpFast (full tgt d s len:ℕ) (slices:BT SliceData) (syms:BT SymData)
    (nextLv:BT CertNode) (u:CertNode) (ws:List ℕ)
    (pruneInfo:List (SliceData × ℕ × ℕ × List Bool))
    (i j:ℕ) (a b:ℕ) (d1i d1j d2ij:List (ℕ × ℕ)) (op:ℕ) (r:ℕ):Bool :=
  let z:=normWFast full r
  if z == 0 || z == full || ws.contains z then true
  else if z == tgt then false
  else
    let mcBase:=((i * 16 + j) * 4 + op) * 4
    let u1:=if len > s then false else zUnsepAny z d1j
    let ok1 :=
      if len > s || u1 then true
      else if checkPruneFast s pruneInfo z i j false true then true
      else checkEdge d slices syms nextLv u (mkCand ws a b z 1) z (mcBase + 1)
    if !ok1 then false else
    let u2:=if len > s then false else zUnsepAny z d1i
    let ok2 :=
      if len > s || u2 then true
      else if checkPruneFast s pruneInfo z i j true false then true
      else checkEdge d slices syms nextLv u (mkCand ws a b z 2) z (mcBase + 2)
    if !ok2 then false else
    let ok0 :=
      if len - 1 > s || u1 || u2 then true
      else if zUnsepAny z d2ij then true
      else if checkPruneFast s pruneInfo z i j true true then true
      else checkEdge d slices syms nextLv u (mkCand ws a b z 0) z mcBase
    if !ok0 then false else
    if len + 1 > s then true
    else if checkPruneFast s pruneInfo z i j false false then true
    else checkEdge d slices syms nextLv u (mkCand ws a b z 3) z (mcBase + 3)
def loopJFast (full tgt d s len:ℕ) (slices:BT SliceData) (syms:BT SymData)
    (nextLv:BT CertNode) (u:CertNode) (ws:List ℕ)
    (pruneInfo:List (SliceData × ℕ × ℕ × List Bool))
    (i:ℕ) (a aNot:ℕ) (d1i:List (ℕ × ℕ))
   :ℕ -> List ℕ -> List (List (ℕ × ℕ)) -> List (ℕ × ℕ × List ℕ × List ℕ) -> Bool
  | _,[],_,_ => true
  | j,b :: restJ,d1Rest,jStates =>
    let d1j:=match d1Rest with | h :: _ => h | [] => []
    let d1Tail:=match d1Rest with | _ :: t => t | [] => []
    let d2ij :=
      if len - 1 > s then []
      else jStates.filterMap fun st =>
        match st.2.2.2 with
        | su :: _ => let m:=st.2.1 &&& su; if m == 0 then none else some (st.1,m)
        | [] => none
    let bNot:=b ^^^ full
    if !checkOneOpFast full tgt d s len slices syms nextLv u ws pruneInfo i j a b d1i d1j d2ij 0 (a &&& b) then false
    else if !checkOneOpFast full tgt d s len slices syms nextLv u ws pruneInfo i j a b d1i d1j d2ij 1 (a ||| b) then false
    else if !checkOneOpFast full tgt d s len slices syms nextLv u ws pruneInfo i j a b d1i d1j d2ij 2 (a &&& bNot) then false
    else if !checkOneOpFast full tgt d s len slices syms nextLv u ws pruneInfo i j a b d1i d1j d2ij 3 (aNot &&& b) then false
    else
      let nextJStates :=
        if len - 1 > s then []
        else jStates.filterMap fun st =>
          match st.2.2.1,st.2.2.2 with
          | l :: lt,_ :: stail =>
            let m:=st.2.1 &&& l
            if m == 0 then none else some (st.1,m,lt,stail)
          | _,_ => none
      loopJFast full tgt d s len slices syms nextLv u ws pruneInfo i a aNot d1i (j + 1) restJ d1Tail nextJStates
def loopIFast (full tgt d s len:ℕ) (slices:BT SliceData) (syms:BT SymData)
    (nextLv:BT CertNode) (u:CertNode) (ws:List ℕ)
    (pruneInfo:List (SliceData × ℕ × ℕ × List Bool))
   :ℕ -> List ℕ -> List (List (ℕ × ℕ)) -> List (ℕ × ℕ × List ℕ × List ℕ) -> Bool
  | _,[],_,_ => true
  | i,a :: restI,d1All,iStates =>
    let d1i:=match d1All with | h :: _ => h | [] => []
    let d1Tail:=match d1All with | _ :: t => t | [] => []
    let jStates :=
      if len - 1 > s then []
      else iStates.filterMap fun st =>
        match st.2.2.1,st.2.2.2 with
        | _ :: lt,_ :: stail => some (st.1,st.2.1,lt,stail)
        | _,_ => none
    if !loopJFast full tgt d s len slices syms nextLv u ws pruneInfo i a (a ^^^ full) d1i (i + 1) restI d1Tail jStates then false
    else
      let nextIStates :=
        if len - 1 > s then []
        else iStates.filterMap fun st =>
          match st.2.2.1,st.2.2.2 with
          | l :: lt,_ :: stail =>
            let m:=st.2.1 &&& l
            if m == 0 then none else some (st.1,m,lt,stail)
          | _,_ => none
      loopIFast full tgt d s len slices syms nextLv u ws pruneInfo (i + 1) restI d1Tail nextIStates
def checkNodeFast (n tgt cap d nSlices:ℕ) (zs:List ℕ) (slices:BT SliceData) (syms:BT SymData)
    (nextLv:BT CertNode) (u:CertNode):Bool :=
  let full:=maskN n
  let s:=cap - d
  let ws:=u.ws
  let len:=ws.length
  (!ws.contains tgt) &&
  ws.Nodup &&
  (ws.all fun w => (w &&& full) == w) &&
  (u.zs.all fun k0 => zs.contains k0) &&
  (if s ≤ 1 then
    (List.range len).all fun i =>
      (List.range len).all fun j =>
        if j ≤ i then true
        else
          let a:=ws.getD i 0
          let b:=ws.getD j 0
          (List.range 4).all fun op =>
            let z:=applyOp full op a b
            if z == 0 || z == full || ws.contains z then true
            else z != tgt
  else
    let initStates :=
      if len - 1 > s then []
      else u.zs.map fun k0 =>
        let bit:=1 <<< k0
        let ls:=ws.map fun w => if (w &&& bit) != 0 then w else w ^^^ full
        let ss:=(sufAnd full ls).2
        (bit,tgt,ls,ss)
    let d1All:=if len > s then [] else buildDrop1 initStates len
    let pruneInfo:=u.prune.filterMap fun ri =>
      if ri < nSlices then
        match btGet slices ri with
        | some sl =>
          let pOld:=paidOf d u.paid ri
          let cFlags:=ws.map fun w => projSl sl w == 0
          let ccAll:=(cFlags.filter id).length
          some (sl,pOld,ccAll,cFlags)
        | none => none
      else none
    loopIFast full tgt d s len slices syms nextLv u ws pruneInfo 0 ws d1All initStates)
theorem isUnsep_of_perm_cons {full tgt:ℕ} {zs:List ℕ} {a:ℕ} {l1 l2:List ℕ}
    (hp:l2.Perm (a :: l1)) (h:isUnsep full tgt zs l2 = true) :
    isUnsep full tgt zs l1 = true:=by
  unfold isUnsep at h ⊢
  rw [List.any_eq_true] at h ⊢
  obtain ⟨k0,hk0,h1⟩:=h
  refine ⟨k0,hk0,?_⟩
  rw [isUnsepOne_eq_foldl,foldl_unsep_eq_map,bne_iff_ne] at h1 ⊢
  rw [foldl_and_perm (hp.map _),List.map_cons] at h1
  exact foldl_and_ne_zero_of_cons h1
theorem checkPruneFast_sound (d s nSlices:ℕ) (slices:BT SliceData) (u:CertNode)
    (hnd:u.ws.Nodup) (i j:ℕ) (hij:i < j) (hj:j < u.ws.length) (z:ℕ)
    (pruneInfo:List (SliceData × ℕ × ℕ × List Bool))
    (hpi:∀ p ∈ pruneInfo,
      ∃ ri ∈ u.prune,ri < nSlices /\ btGet slices ri = some p.1 /\
        p.2.1 = paidOf d u.paid ri /\
        p.2.2.1 = countConst p.1 u.ws /\
        p.2.2.2 = u.ws.map (fun w => projSl p.1 w == 0))
    (kc:ℕ) (dropA dropB:Bool)
    (hkc:(kc = 0 /\ dropA = true /\ dropB = true) \/
           (kc = 1 /\ dropA = false /\ dropB = true) \/
           (kc = 2 /\ dropA = true /\ dropB = false) \/
           (kc = 3 /\ dropA = false /\ dropB = false))
    (h:checkPruneFast s pruneInfo z i j dropA dropB = true) :
    u.prune.any (fun ri =>
      if ri < nSlices then
        match btGet slices ri with
        | some sl =>
          let pr:=projSl sl z
          let zA:=if pr != 0 && !sl.base.contains pr then 1 else 0
          let pNew:=paidOf d u.paid ri + zA
          sl.L + countConst sl (mkCand u.ws (u.ws.getD i 0) (u.ws.getD j 0) z kc) > pNew + (s - 1)
        | none => false
      else false) = true:=by
  unfold checkPruneFast at h
  rw [List.any_eq_true] at h ⊢
  obtain ⟨⟨sl,pOld,ccAll,cFlags⟩,hmem,hgt⟩:=h
  obtain ⟨ri,hri_mem,hri_lt,hbt,hpOld,hccAll,hcFlags⟩:=hpi _ hmem
  dsimp only at hbt hpOld hccAll hcFlags
  refine ⟨ri,hri_mem,?_⟩
  simp only [hri_lt,↓reduceIte,hbt,decide_eq_true_eq] at hgt ⊢
  have hi:i < u.ws.length:=by omega
  have hfi:cFlags.getD i false = (projSl sl (u.ws.getD i 0) == 0):=by
    rw [hcFlags]; simp [List.getD_eq_getElem?_getD,hi]
  have hfj:cFlags.getD j false = (projSl sl (u.ws.getD j 0) == 0):=by
    rw [hcFlags]; simp [List.getD_eq_getElem?_getD,hj]
  have hccs:=countConst_mkCand sl u.ws hnd i j hij hj z
  rw [hpOld,hccAll,hfi,hfj] at hgt
  rcases hkc with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · rw [hccs.1]; simpa using hgt
  · rw [hccs.2.1]; simpa using hgt
  · rw [hccs.2.2.1]; simpa using hgt
  · rw [hccs.2.2.2]; simpa using hgt
theorem checkOneOpFast_sound (full tgt d s nSlices:ℕ) (zs:List ℕ)
    (slices:BT SliceData) (syms:BT SymData) (nextLv:BT CertNode) (u:CertNode)
    (htgt_mask:tgt &&& full = tgt)
    (hnd:u.ws.Nodup) (hs:¬ s ≤ 1)
    (pruneInfo:List (SliceData × ℕ × ℕ × List Bool))
    (hpi:∀ p ∈ pruneInfo,
      ∃ ri ∈ u.prune,ri < nSlices /\ btGet slices ri = some p.1 /\
        p.2.1 = paidOf d u.paid ri /\
        p.2.2.1 = countConst p.1 u.ws /\
        p.2.2.2 = u.ws.map (fun w => projSl p.1 w == 0))
    (i j:ℕ) (hij:i < j) (hj:j < u.ws.length)
    (d1i d1j d2ij:List (ℕ × ℕ))
    (hd1i:∀ p ∈ d1i,PairInv full tgt zs (u.ws.erase (u.ws.getD i 0)) p)
    (hd1j:∀ p ∈ d1j,PairInv full tgt zs (u.ws.erase (u.ws.getD j 0)) p)
    (hd2ij:∀ p ∈ d2ij,PairInv full tgt zs ((u.ws.erase (u.ws.getD i 0)).erase (u.ws.getD j 0)) p)
    (op r:ℕ) (hr:normW full r = applyOp full op (u.ws.getD i 0) (u.ws.getD j 0))
    (hok:checkOneOpFast full tgt d s u.ws.length slices syms nextLv u u.ws pruneInfo
             i j (u.ws.getD i 0) (u.ws.getD j 0) d1i d1j d2ij op r = true) :
    let a:=u.ws.getD i 0
    let b:=u.ws.getD j 0
    let z:=applyOp full op a b
    (if z == 0 || z == full || u.ws.contains z then true
     else if z == tgt then false
     else if s ≤ 1 then true
     else (List.range 4).all fun kc =>
       checkCand full tgt d s nSlices zs slices syms nextLv u (mkCand u.ws a b z kc) z
         (((i * 16 + j) * 4 + op) * 4 + kc)) = true:=by
  dsimp only
  unfold checkOneOpFast at hok
  rw [normWFast_eq_normW,hr] at hok
  set a:=u.ws.getD i 0
  set b:=u.ws.getD j 0
  set z:=applyOp full op a b
  dsimp only at hok
  cases hskip:(z == 0 || z == full || u.ws.contains z) with
  | true => simp [hskip]
  | false =>
    simp only [hskip,Bool.false_eq_true,↓reduceIte] at hok ⊢
    by_cases hztgt:(z == tgt) = true
    · simp [hztgt] at hok
    have hztgt_f:(z == tgt) = false:=Bool.eq_false_iff.2 hztgt
    simp only [hztgt_f,hs,Bool.false_eq_true,↓reduceIte] at hok ⊢
    have hi:i < u.ws.length:=by omega
    have ha_eq:a = u.ws[i]:=by simp [a,List.getD_eq_getElem?_getD,hi]
    have hb_eq:b = u.ws[j]:=by simp [b,List.getD_eq_getElem?_getD,hj]
    have ha_mem:a ∈ u.ws:=by rw [ha_eq]; exact List.getElem_mem hi
    have hb_mem:b ∈ u.ws:=by rw [hb_eq]; exact List.getElem_mem hj
    have hab:a ≠ b:=by
      rw [ha_eq,hb_eq]
      intro heq; have:=(List.Nodup.getElem_inj_iff hnd).1 heq; omega
    have ha_mem':a ∈ u.ws.erase b:=(List.mem_erase_of_ne hab).2 ha_mem
    have hb_mem':b ∈ u.ws.erase a:=(List.mem_erase_of_ne hab.symm).2 hb_mem
    have hperm0:(mkCand u.ws a b z 0).Perm (z :: (u.ws.erase a).erase b):=by
      simp only [mkCand]; exact List.perm_append_singleton z _
    have hperm1:(mkCand u.ws a b z 1).Perm (z :: u.ws.erase b):=by
      simp only [mkCand]
      have h1:((u.ws.erase a).erase b ++ [z] ++ [a]).Perm (z :: a :: (u.ws.erase a).erase b) :=
        (List.perm_append_singleton a _).trans
          ((List.Perm.cons a (List.perm_append_singleton z _)).trans (List.Perm.swap z a _))
      have h2:(a :: (u.ws.erase a).erase b).Perm (u.ws.erase b):=by
        rw [List.erase_comm]; exact (List.perm_cons_erase ha_mem').symm
      exact h1.trans (List.Perm.cons z h2)
    have hperm2:(mkCand u.ws a b z 2).Perm (z :: u.ws.erase a):=by
      simp only [mkCand]
      have h1:((u.ws.erase a).erase b ++ [z] ++ [b]).Perm (z :: b :: (u.ws.erase a).erase b) :=
        (List.perm_append_singleton b _).trans
          ((List.Perm.cons b (List.perm_append_singleton z _)).trans (List.Perm.swap z b _))
      exact h1.trans (List.Perm.cons z (List.perm_cons_erase hb_mem').symm)
    have hlens:=mkCand_lengths u.ws hnd i j hij hj z
    have hsplit4:∀ {b1 b2 b0 b3:Bool},
        (if (!b1) = true then false else if (!b2) = true then false else if (!b0) = true then false else b3) = true ->
        b1 = true /\ b2 = true /\ b0 = true /\ b3 = true:=by
      intro b1 b2 b0 b3 hh; cases b1 <;> cases b2 <;> cases b0 <;> simp at hh ⊢; exact hh
    obtain ⟨hok1,hok2,hok0,hok3⟩:=hsplit4 hok
    have hu1_unsep:(if u.ws.length > s then false else zUnsepAny z d1j) = true ->
        isUnsep full tgt zs (mkCand u.ws a b z 1) = true:=by
      intro h1
      by_cases hgt:u.ws.length > s
      · simp [hgt] at h1
      · simp only [hgt,↓reduceIte] at h1
        exact zUnsepAny_sound full tgt z zs (u.ws.erase b) (mkCand u.ws a b z 1) htgt_mask hperm1 d1j hd1j h1
    have hu2_unsep:(if u.ws.length > s then false else zUnsepAny z d1i) = true ->
        isUnsep full tgt zs (mkCand u.ws a b z 2) = true:=by
      intro h2
      by_cases hgt:u.ws.length > s
      · simp [hgt] at h2
      · simp only [hgt,↓reduceIte] at h2
        exact zUnsepAny_sound full tgt z zs (u.ws.erase a) (mkCand u.ws a b z 2) htgt_mask hperm2 d1i hd1i h2
    have hite_else:∀ {p:Prop} [Decidable p] {c:Bool},c = true -> (if p then true else c) = true:=by
      intro p _ c hc; split_ifs <;> [rfl; exact hc]
    rw [List.all_eq_true]
    intro kc hkc_mem
    rw [List.mem_range] at hkc_mem
    unfold checkCand
    match kc with
    | 0 =>
      simp only [Nat.add_zero]
      rw [hlens.1]
      by_cases hgt:u.ws.length - 1 > s
      · simp [hgt]
      · simp only [hgt,↓reduceIte]
        by_cases h1:(if u.ws.length > s then false else zUnsepAny z d1j) = true
        · have hun1:=hu1_unsep h1
          have hsub:(mkCand u.ws a b z 1).Perm (a :: mkCand u.ws a b z 0):=by
            simp only [mkCand]; exact List.perm_append_singleton a _
          simp [isUnsep_of_perm_cons hsub hun1]
        · by_cases h2:(if u.ws.length > s then false else zUnsepAny z d1i) = true
          · have hun2:=hu2_unsep h2
            have hsub:(mkCand u.ws a b z 2).Perm (b :: mkCand u.ws a b z 0):=by
              simp only [mkCand]; exact List.perm_append_singleton b _
            simp [isUnsep_of_perm_cons hsub hun2]
          · have h1f:(if u.ws.length > s then false else zUnsepAny z d1j) = false:=Bool.eq_false_iff.2 h1
            have h2f:(if u.ws.length > s then false else zUnsepAny z d1i) = false:=Bool.eq_false_iff.2 h2
            simp only [h1f,h2f,hgt,decide_false,Bool.or_false,Bool.false_eq_true,↓reduceIte] at hok0
            by_cases hz0:zUnsepAny z d2ij = true
            · simp [zUnsepAny_sound full tgt z zs ((u.ws.erase a).erase b) (mkCand u.ws a b z 0) htgt_mask hperm0 d2ij hd2ij hz0]
            · simp only [hz0,↓reduceIte] at hok0
              by_cases hp0:checkPruneFast s pruneInfo z i j true true = true
              · have hp:=checkPruneFast_sound d s nSlices slices u hnd i j hij hj z pruneInfo hpi 0 true true (Or.inl ⟨rfl,rfl,rfl⟩) hp0
                exact hite_else (by simp only [a,b]; rw [hp]; rfl)
              · simp only [hp0,↓reduceIte] at hok0
                exact hite_else (hite_else hok0)
    | 1 =>
      rw [hlens.2.1]
      by_cases hgt:u.ws.length > s
      · simp [hgt]
      · simp only [hgt,↓reduceIte]
        by_cases h1:(if u.ws.length > s then false else zUnsepAny z d1j) = true
        · simp [hu1_unsep h1]
        · have h1f:(if u.ws.length > s then false else zUnsepAny z d1j) = false:=Bool.eq_false_iff.2 h1
          simp only [hgt,↓reduceIte] at h1f
          simp only [hgt,decide_false,h1f,Bool.false_or,Bool.false_eq_true,↓reduceIte] at hok1
          by_cases hp1:checkPruneFast s pruneInfo z i j false true = true
          · have hp:=checkPruneFast_sound d s nSlices slices u hnd i j hij hj z pruneInfo hpi 1 false true (Or.inr (Or.inl ⟨rfl,rfl,rfl⟩)) hp1
            exact hite_else (by simp only [a,b]; rw [hp]; rfl)
          · simp only [hp1,↓reduceIte] at hok1
            exact hite_else (hite_else hok1)
    | 2 =>
      rw [hlens.2.2.1]
      by_cases hgt:u.ws.length > s
      · simp [hgt]
      · simp only [hgt,↓reduceIte]
        by_cases h2:(if u.ws.length > s then false else zUnsepAny z d1i) = true
        · simp [hu2_unsep h2]
        · have h2f:(if u.ws.length > s then false else zUnsepAny z d1i) = false:=Bool.eq_false_iff.2 h2
          simp only [hgt,↓reduceIte] at h2f
          simp only [hgt,decide_false,h2f,Bool.false_or,Bool.false_eq_true,↓reduceIte] at hok2
          by_cases hp2:checkPruneFast s pruneInfo z i j true false = true
          · have hp:=checkPruneFast_sound d s nSlices slices u hnd i j hij hj z pruneInfo hpi 2 true false (Or.inr (Or.inr (Or.inl ⟨rfl,rfl,rfl⟩))) hp2
            exact hite_else (by simp only [a,b]; rw [hp]; rfl)
          · simp only [hp2,↓reduceIte] at hok2
            exact hite_else (hite_else hok2)
    | 3 =>
      rw [hlens.2.2.2]
      by_cases hgt:u.ws.length + 1 > s
      · simp [hgt]
      · simp only [hgt,↓reduceIte] at hok3 ⊢
        by_cases hp3:checkPruneFast s pruneInfo z i j false false = true
        · have hp:=checkPruneFast_sound d s nSlices slices u hnd i j hij hj z pruneInfo hpi 3 false false (Or.inr (Or.inr (Or.inr ⟨rfl,rfl,rfl⟩))) hp3
          exact hite_else (by simp only [a,b]; rw [hp]; rfl)
        · simp only [hp3,↓reduceIte] at hok3
          exact hite_else (hite_else hok3)
    | _ + 4 => omega
theorem perm_erase_split {α:Type} [DecidableEq α] (pre post:List α) (x:α)
    (hnd:(pre ++ x :: post).Nodup) :
    ((pre ++ x :: post).erase x).Perm (pre ++ post):=by
  have h1:(pre ++ x :: post).Perm (x :: (pre ++ post)):=List.perm_middle
  have h2:((pre ++ x :: post).erase x).Perm ((x :: (pre ++ post)).erase x) :=
    h1.erase x
  simpa using h2
theorem pairInv_perm {full tgt:ℕ} {zs s1 s2:List ℕ} (hp:s1.Perm s2) {p:ℕ × ℕ}
    (h:PairInv full tgt zs s1 p):PairInv full tgt zs s2 p:=by
  obtain ⟨k0,hk0,hbit,hne,heq⟩:=h
  exact ⟨k0,hk0,hbit,hne,heq.trans (foldl_and_perm (hp.map _) tgt)⟩
theorem loopJFast_sound (full tgt d s nSlices:ℕ) (zs:List ℕ)
    (slices:BT SliceData) (syms:BT SymData) (nextLv:BT CertNode) (u:CertNode)
    (htgt_mask:tgt &&& full = tgt) (hnd:u.ws.Nodup) (hs:¬ s ≤ 1)
    (pruneInfo:List (SliceData × ℕ × ℕ × List Bool))
    (hpi:∀ p ∈ pruneInfo,
      ∃ ri ∈ u.prune,ri < nSlices /\ btGet slices ri = some p.1 /\
        p.2.1 = paidOf d u.paid ri /\
        p.2.2.1 = countConst p.1 u.ws /\
        p.2.2.2 = u.ws.map (fun w => projSl p.1 w == 0))
    (preI:List ℕ) (a:ℕ) (d1i:List (ℕ × ℕ))
    (hd1i:∀ p ∈ d1i,PairInv full tgt zs (u.ws.erase a) p) :
    ∀ (restJ mid:List ℕ) (d1Rest:List (List (ℕ × ℕ))) (jStates:List (ℕ × ℕ × List ℕ × List ℕ)),
      u.ws = preI ++ a :: (mid ++ restJ) ->
      D1Inv full tgt zs (preI ++ [a] ++ mid) restJ d1Rest ->
      (∀ st ∈ jStates,ZInv full tgt zs (preI ++ mid) restJ st) ->
      loopJFast full tgt d s u.ws.length slices syms nextLv u u.ws pruneInfo
        preI.length a (a ^^^ full) d1i (preI.length + 1 + mid.length) restJ d1Rest jStates = true ->
      ∀ j,preI.length + 1 + mid.length ≤ j -> j < u.ws.length ->
        ∀ op < 4,
          let a':=u.ws.getD preI.length 0
          let b':=u.ws.getD j 0
          let z:=applyOp full op a' b'
          (if z == 0 || z == full || u.ws.contains z then true
           else if z == tgt then false
           else if s ≤ 1 then true
           else (List.range 4).all fun kc =>
             checkCand full tgt d s nSlices zs slices syms nextLv u (mkCand u.ws a' b' z kc) z
               (((preI.length * 16 + j) * 4 + op) * 4 + kc)) = true:=by
  intro restJ
  induction restJ with
  | nil =>
    intro mid d1Rest jStates hws _ _ _ j hjlo hjhi
    rw [hws] at hjhi
    simp at hjhi
    omega
  | cons b restJ ih =>
    intro mid d1Rest jStates hws hd1 hjst hok j hjlo hjhi op hop
    unfold loopJFast at hok
    dsimp only at hok
    set j0:=preI.length + 1 + mid.length
    have ha_at:u.ws.getD preI.length 0 = a:=by
      rw [hws]; simp [List.getD_eq_getElem?_getD,List.getElem?_append]
    have hb_at:u.ws.getD j0 0 = b:=by
      have hws':u.ws = (preI ++ [a] ++ mid) ++ b :: restJ:=by simp [hws]
      have hlen_pre:(preI ++ [a] ++ mid).length = j0:=by simp [j0]; omega
      rw [hws',<- hlen_pre]; simp [List.getD_eq_getElem?_getD,List.getElem?_append]
    set d1j:=match d1Rest with | h :: _ => h | [] => []
    set d1Tail:=match d1Rest with | _ :: t => t | [] => []
    set d2ij:=if u.ws.length - 1 > s then [] else jStates.filterMap fun st =>
      match st.2.2.2 with | su :: _ => let m:=st.2.1 &&& su; if m == 0 then none else some (st.1,m) | [] => none
    set nextJStates:=if u.ws.length - 1 > s then [] else jStates.filterMap fun st =>
      match st.2.2.1,st.2.2.2 with
      | l :: lt,_ :: stail => let m:=st.2.1 &&& l; if m == 0 then none else some (st.1,m,lt,stail)
      | _,_ => none
    have hsplit :
        checkOneOpFast full tgt d s u.ws.length slices syms nextLv u u.ws pruneInfo preI.length j0 a b d1i d1j d2ij 0 (a &&& b) = true /\
        checkOneOpFast full tgt d s u.ws.length slices syms nextLv u u.ws pruneInfo preI.length j0 a b d1i d1j d2ij 1 (a ||| b) = true /\
        checkOneOpFast full tgt d s u.ws.length slices syms nextLv u u.ws pruneInfo preI.length j0 a b d1i d1j d2ij 2 (a &&& (b ^^^ full)) = true /\
        checkOneOpFast full tgt d s u.ws.length slices syms nextLv u u.ws pruneInfo preI.length j0 a b d1i d1j d2ij 3 ((a ^^^ full) &&& b) = true /\
        loopJFast full tgt d s u.ws.length slices syms nextLv u u.ws pruneInfo preI.length a (a ^^^ full) d1i (j0 + 1) restJ d1Tail nextJStates = true:=by
      have hc0:checkOneOpFast full tgt d s u.ws.length slices syms nextLv u u.ws pruneInfo preI.length j0 a b d1i d1j d2ij 0 (a &&& b) = true:=by
        cases h:checkOneOpFast full tgt d s u.ws.length slices syms nextLv u u.ws pruneInfo preI.length j0 a b d1i d1j d2ij 0 (a &&& b) <;> simp [h] at hok ⊢
      simp only [hc0,Bool.not_true,Bool.false_eq_true,↓reduceIte] at hok
      have hc1:checkOneOpFast full tgt d s u.ws.length slices syms nextLv u u.ws pruneInfo preI.length j0 a b d1i d1j d2ij 1 (a ||| b) = true:=by
        cases h:checkOneOpFast full tgt d s u.ws.length slices syms nextLv u u.ws pruneInfo preI.length j0 a b d1i d1j d2ij 1 (a ||| b) <;> simp [h] at hok ⊢
      simp only [hc1,Bool.not_true,Bool.false_eq_true,↓reduceIte] at hok
      have hc2:checkOneOpFast full tgt d s u.ws.length slices syms nextLv u u.ws pruneInfo preI.length j0 a b d1i d1j d2ij 2 (a &&& (b ^^^ full)) = true:=by
        cases h:checkOneOpFast full tgt d s u.ws.length slices syms nextLv u u.ws pruneInfo preI.length j0 a b d1i d1j d2ij 2 (a &&& (b ^^^ full)) <;> simp [h] at hok ⊢
      simp only [hc2,Bool.not_true,Bool.false_eq_true,↓reduceIte] at hok
      have hc3:checkOneOpFast full tgt d s u.ws.length slices syms nextLv u u.ws pruneInfo preI.length j0 a b d1i d1j d2ij 3 ((a ^^^ full) &&& b) = true:=by
        cases h:checkOneOpFast full tgt d s u.ws.length slices syms nextLv u u.ws pruneInfo preI.length j0 a b d1i d1j d2ij 3 ((a ^^^ full) &&& b) <;> simp [h] at hok ⊢
      simp only [hc3,Bool.not_true,Bool.false_eq_true,↓reduceIte] at hok
      exact ⟨hc0,hc1,hc2,hc3,hok⟩
    by_cases hjeq:j = j0
    · subst hjeq
      have hws':u.ws = (preI ++ [a] ++ mid) ++ b :: restJ:=by simp [hws]
      have hd1j_inv:∀ p ∈ d1j,
          PairInv full tgt zs (u.ws.erase (u.ws.getD j0 0)) p:=by
        rw [hb_at]
        have hp_b:(u.ws.erase b).Perm ((preI ++ [a] ++ mid) ++ restJ):=by
          rw [hws']; exact perm_erase_split (preI ++ [a] ++ mid) restJ b (hws' ▸ hnd)
        intro p hp
        cases d1Rest with
        | nil => simp [d1j] at hp
        | cons h t => exact pairInv_perm hp_b.symm (hd1.1 p hp)
      have hd2_inv:∀ p ∈ d2ij,
          PairInv full tgt zs ((u.ws.erase (u.ws.getD preI.length 0)).erase (u.ws.getD j0 0)) p:=by
        rw [ha_at,hb_at]
        simp only [d2ij]
        split_ifs with hgt
        · intro p hp; cases hp
        · intro p hp
          have hraw:=extract_d_inv full tgt zs (preI ++ mid) b restJ htgt_mask jStates hjst p hp
          have hp_a:(u.ws.erase a).Perm (preI ++ (mid ++ b :: restJ)):=by
            rw [hws]; exact perm_erase_split preI (mid ++ b :: restJ) a (hws ▸ hnd)
          have hnd_a:(preI ++ mid ++ b :: restJ).Nodup:=by
            have:=hp_a.nodup_iff.1 (hnd.erase a)
            simpa [List.append_assoc] using this
          have hp_ab:((u.ws.erase a).erase b).Perm ((preI ++ mid) ++ restJ):=by
            have h1:((u.ws.erase a).erase b).Perm ((preI ++ mid ++ b :: restJ).erase b):=by
              have hp_a':(u.ws.erase a).Perm (preI ++ mid ++ b :: restJ):=by simpa [List.append_assoc] using hp_a
              exact hp_a'.erase b
            exact h1.trans (perm_erase_split (preI ++ mid) restJ b hnd_a)
          exact pairInv_perm hp_ab.symm hraw
      have hcall:∀ op' r',normW full r' = applyOp full op' (u.ws.getD preI.length 0) (u.ws.getD j0 0) ->
          checkOneOpFast full tgt d s u.ws.length slices syms nextLv u u.ws pruneInfo preI.length j0 a b d1i d1j d2ij op' r' = true ->
          let a':=u.ws.getD preI.length 0
          let b':=u.ws.getD j0 0
          let z:=applyOp full op' a' b'
          (if z == 0 || z == full || u.ws.contains z then true
           else if z == tgt then false
           else if s ≤ 1 then true
           else (List.range 4).all fun kc =>
             checkCand full tgt d s nSlices zs slices syms nextLv u (mkCand u.ws a' b' z kc) z
               (((preI.length * 16 + j0) * 4 + op') * 4 + kc)) = true:=by
        intro op' r' hr' hok'
        exact checkOneOpFast_sound full tgt d s nSlices zs slices syms nextLv u htgt_mask hnd hs pruneInfo hpi
          preI.length j0 (by omega) hjhi d1i d1j d2ij (by rw [ha_at]; exact hd1i) hd1j_inv hd2_inv op' r' hr'
          (by rw [ha_at,hb_at]; exact hok')
      match op with
      | 0 => exact hcall 0 (a &&& b) (by rw [ha_at,hb_at]; rfl) hsplit.1
      | 1 => exact hcall 1 (a ||| b) (by rw [ha_at,hb_at]; rfl) hsplit.2.1
      | 2 => exact hcall 2 (a &&& (b ^^^ full)) (by rw [ha_at,hb_at]; rfl) hsplit.2.2.1
      | 3 => exact hcall 3 ((a ^^^ full) &&& b) (by rw [ha_at,hb_at]; rfl) hsplit.2.2.2.1
      | _ + 4 => omega
    · have hws_next:u.ws = preI ++ a :: ((mid ++ [b]) ++ restJ):=by simp [hws]
      have hd1_next:D1Inv full tgt zs (preI ++ [a] ++ (mid ++ [b])) restJ d1Tail:=by
        simpa [List.append_assoc,d1Tail] using hd1.2
      have hjst_next:∀ st' ∈ nextJStates,ZInv full tgt zs (preI ++ (mid ++ [b])) restJ st':=by
        simp only [nextJStates]
        split_ifs
        · intro _ h; cases h
        · intro st' hst'
          simpa [List.append_assoc] using step_states_inv full tgt zs (preI ++ mid) b restJ jStates hjst st' hst'
      have hidx:preI.length + 1 + (mid ++ [b]).length = j0 + 1:=by simp [j0]; omega
      exact ih (mid ++ [b]) d1Tail nextJStates hws_next hd1_next hjst_next (by rw [hidx]; exact hsplit.2.2.2.2)
        j (by omega) hjhi op hop
theorem loopIFast_sound (full tgt d s nSlices:ℕ) (zs:List ℕ)
    (slices:BT SliceData) (syms:BT SymData) (nextLv:BT CertNode) (u:CertNode)
    (htgt_mask:tgt &&& full = tgt) (hnd:u.ws.Nodup) (hs:¬ s ≤ 1)
    (pruneInfo:List (SliceData × ℕ × ℕ × List Bool))
    (hpi:∀ p ∈ pruneInfo,
      ∃ ri ∈ u.prune,ri < nSlices /\ btGet slices ri = some p.1 /\
        p.2.1 = paidOf d u.paid ri /\
        p.2.2.1 = countConst p.1 u.ws /\
        p.2.2.2 = u.ws.map (fun w => projSl p.1 w == 0)) :
    ∀ (restI preI:List ℕ) (d1All:List (List (ℕ × ℕ))) (iStates:List (ℕ × ℕ × List ℕ × List ℕ)),
      u.ws = preI ++ restI ->
      D1Inv full tgt zs preI restI d1All ->
      (∀ st ∈ iStates,ZInv full tgt zs preI restI st) ->
      loopIFast full tgt d s u.ws.length slices syms nextLv u u.ws pruneInfo
        preI.length restI d1All iStates = true ->
      ∀ i,preI.length ≤ i -> i < u.ws.length ->
        ∀ j < u.ws.length,i < j ->
          ∀ op < 4,
            let a':=u.ws.getD i 0
            let b':=u.ws.getD j 0
            let z:=applyOp full op a' b'
            (if z == 0 || z == full || u.ws.contains z then true
             else if z == tgt then false
             else if s ≤ 1 then true
             else (List.range 4).all fun kc =>
               checkCand full tgt d s nSlices zs slices syms nextLv u (mkCand u.ws a' b' z kc) z
                 (((i * 16 + j) * 4 + op) * 4 + kc)) = true:=by
  intro restI
  induction restI with
  | nil =>
    intro preI _ _ hws _ _ _ i hilo hihi
    rw [hws] at hihi; simp at hihi; omega
  | cons a restI ih =>
    intro preI d1All iStates hws hd1 hist hok i hilo hihi j hj hij op hop
    unfold loopIFast at hok
    dsimp only at hok
    set d1i:=match d1All with | h :: _ => h | [] => []
    set d1Tail:=match d1All with | _ :: t => t | [] => []
    set jStates:=if u.ws.length - 1 > s then [] else iStates.filterMap fun st =>
      match st.2.2.1,st.2.2.2 with | _ :: lt,_ :: stail => some (st.1,st.2.1,lt,stail) | _,_ => none
    set nextIStates:=if u.ws.length - 1 > s then [] else iStates.filterMap fun st =>
      match st.2.2.1,st.2.2.2 with
      | l :: lt,_ :: stail => let m:=st.2.1 &&& l; if m == 0 then none else some (st.1,m,lt,stail)
      | _,_ => none
    have hsplit :
        loopJFast full tgt d s u.ws.length slices syms nextLv u u.ws pruneInfo preI.length a (a ^^^ full) d1i (preI.length + 1) restI d1Tail jStates = true /\
        loopIFast full tgt d s u.ws.length slices syms nextLv u u.ws pruneInfo (preI.length + 1) restI d1Tail nextIStates = true:=by
      have hj0:loopJFast full tgt d s u.ws.length slices syms nextLv u u.ws pruneInfo preI.length a (a ^^^ full) d1i (preI.length + 1) restI d1Tail jStates = true:=by
        cases h:loopJFast full tgt d s u.ws.length slices syms nextLv u u.ws pruneInfo preI.length a (a ^^^ full) d1i (preI.length + 1) restI d1Tail jStates <;> simp [h] at hok ⊢
      simp only [hj0,Bool.not_true,Bool.false_eq_true,↓reduceIte] at hok
      exact ⟨hj0,hok⟩
    by_cases hieq:i = preI.length
    · subst hieq
      have hd1i_inv:∀ p ∈ d1i,
          PairInv full tgt zs (u.ws.erase a) p:=by
        have hp_a:(u.ws.erase a).Perm (preI ++ restI):=by
          rw [hws]; exact perm_erase_split preI restI a (hws ▸ hnd)
        intro p hp
        cases d1All with
        | nil => simp [d1i] at hp
        | cons h t => exact pairInv_perm hp_a.symm (hd1.1 p hp)
      have hjst_inv:∀ st' ∈ jStates,
          ZInv full tgt zs (preI ++ []) restI st':=by
        simp only [jStates]
        split_ifs
        · intro _ h; cases h
        · intro st' hst'; simpa using skip_states_inv full tgt zs preI a restI iStates hist st' hst'
      exact loopJFast_sound full tgt d s nSlices zs slices syms nextLv u htgt_mask hnd hs pruneInfo hpi
        preI a d1i hd1i_inv restI [] d1Tail jStates (by simpa using hws) (by simpa [d1Tail] using hd1.2) hjst_inv
        (by simpa using hsplit.1) j (by simp only [List.length_nil,Nat.add_zero]; omega) hj op hop
    · have hws_next:u.ws = (preI ++ [a]) ++ restI:=by simp [hws]
      have hist_next:∀ st' ∈ nextIStates,ZInv full tgt zs (preI ++ [a]) restI st':=by
        simp only [nextIStates]
        split_ifs
        · intro _ h; cases h
        · exact step_states_inv full tgt zs preI a restI iStates hist
      have hlen_next:(preI ++ [a]).length = preI.length + 1:=by simp
      exact ih (preI ++ [a]) d1Tail nextIStates hws_next (by simpa [d1Tail] using hd1.2) hist_next (by rw [hlen_next]; exact hsplit.2)
        i (by omega) hihi j hj hij op hop
theorem checkNodeFast_implies_checkNode (n tgt cap d nSlices:ℕ) (zs:List ℕ)
    (slices:BT SliceData) (syms:BT SymData) (nextLv:BT CertNode)
    (htgt_mask:tgt &&& maskN n = tgt)
    (u:CertNode)
    (h:checkNodeFast n tgt cap d nSlices zs slices syms nextLv u = true) :
    checkNode n tgt cap d nSlices zs slices syms nextLv u = true:=by
  unfold checkNodeFast at h
  unfold checkNode
  dsimp only at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨hntgt,hnd⟩,hwf⟩,huzs⟩,hbody⟩:=h
  refine ⟨⟨⟨hntgt,hnd⟩,hwf⟩,?_⟩
  by_cases hs:cap - d ≤ 1
  · simp only [hs,↓reduceIte] at hbody
    simp only [List.all_eq_true,List.mem_range] at hbody ⊢
    intro i hi j hj
    have h1:=hbody i hi j hj
    split_ifs at h1 ⊢ with hji
    · rfl
    · simp only [List.all_eq_true,List.mem_range] at h1 ⊢
      intro op hop
      have h2:=h1 op hop
      generalize applyOp (maskN n) op (u.ws.getD i 0) (u.ws.getD j 0) = z at h2 ⊢
      cases hz0:(z == 0 || z == maskN n || u.ws.contains z) <;>
        cases hzt:(z == tgt) <;> simp_all [bne]
  · simp only [hs,↓reduceIte] at hbody
    have hnd_prop:u.ws.Nodup:=of_decide_eq_true hnd
    have huzs_mem:∀ k0 ∈ u.zs,k0 ∈ zs:=by
      simp only [List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at huzs
      exact huzs
    set initStates:=if u.ws.length - 1 > cap - d then []
        else u.zs.map fun k0 =>
          let bit:=1 <<< k0
          let ls:=u.ws.map fun w => if (w &&& bit) != 0 then w else w ^^^ maskN n
          let ss:=(sufAnd (maskN n) ls).2
          (bit,tgt,ls,ss)
    have hinit_inv:∀ st ∈ initStates,ZInv (maskN n) tgt zs [] u.ws st:=by
      simp only [initStates]
      split_ifs
      · intro _ hm; cases hm
      · intro st hst
        rw [List.mem_map] at hst
        obtain ⟨k0,hk0,rfl⟩:=hst
        have hls_eq:(u.ws.map fun w => if (w &&& (1 <<< k0)) != 0 then w else w ^^^ maskN n) =
            u.ws.map (litW (maskN n) k0):=by
          apply List.map_congr_left
          intro w _
          rw [testBit_eq_land_shiftLeft]; rfl
        exact ⟨k0,huzs_mem k0 hk0,rfl,rfl,hls_eq,rfl⟩
    have hd1_inv:D1Inv (maskN n) tgt zs [] u.ws
        (if u.ws.length > cap - d then [] else buildDrop1 initStates u.ws.length):=by
      split_ifs
      · exact d1Inv_nil (maskN n) tgt zs [] u.ws
      · exact buildDrop1_inv (maskN n) tgt zs htgt_mask u.ws [] initStates hinit_inv
    have hpi:∀ p ∈ (u.prune.filterMap fun ri =>
        if ri < nSlices then
          match btGet slices ri with
          | some sl =>
            let pOld:=paidOf d u.paid ri
            let cFlags:=u.ws.map fun w => projSl sl w == 0
            let ccAll:=(cFlags.filter id).length
            some (sl,pOld,ccAll,cFlags)
          | none => none
        else none),
        ∃ ri ∈ u.prune,ri < nSlices /\ btGet slices ri = some p.1 /\
          p.2.1 = paidOf d u.paid ri /\
          p.2.2.1 = countConst p.1 u.ws /\
          p.2.2.2 = u.ws.map (fun w => projSl p.1 w == 0):=by
      intro p hp
      rw [List.mem_filterMap] at hp
      obtain ⟨ri,hri_mem,hri_eq⟩:=hp
      split_ifs at hri_eq with hlt
      · cases hbt:btGet slices ri with
        | none => simp [hbt] at hri_eq
        | some sl =>
          simp only [hbt,Option.some.injEq] at hri_eq
          subst hri_eq
          exact ⟨ri,hri_mem,hlt,hbt,rfl,(countConst_eq_filter_map sl u.ws).symm,rfl⟩
    have hloop:=loopIFast_sound (maskN n) tgt d (cap - d) nSlices zs slices syms nextLv u
      htgt_mask hnd_prop hs _ hpi u.ws [] _ _ rfl hd1_inv hinit_inv hbody
    simp only [List.all_eq_true,List.mem_range]
    intro i hi j hj
    by_cases hji:j ≤ i
    · simp [hji]
    · simp only [hji,↓reduceIte,List.all_eq_true,List.mem_range]
      intro op hop
      exact hloop i (Nat.zero_le i) hi j hj (by omega) op hop
end PEqualNP.Outside.L_meta_10650_aux
namespace PEqualNP.Outside.L_meta_10650_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def allEssCheck (n tgt : ℕ) : Bool :=
  (List.range n).all fun i => isEssOn n (maskN n) tgt i
theorem allEssCheck_sound (n tgt : ℕ) (h : allEssCheck n tgt = true) :
    ∀ i < n,∃ k1 k2,k1 < 1 <<< n /\ k2 < 1 <<< n /\
      (∀ j < n,j ≠ i -> k1.testBit j = k2.testBit j) /\ tgt.testBit k1 ≠ tgt.testBit k2 := by
  intro i hi
  unfold allEssCheck at h
  simp only [List.all_eq_true,List.mem_range] at h
  obtain ⟨k1,k2,hk1,hk2,_,_,hag,hne⟩ := isEssOn_sound n (maskN n) tgt i hi (h i hi)
  exact ⟨k1,k2,hk1,hk2,hag,hne⟩
def zsCheck (n tgt : ℕ) (zs : List ℕ) : Bool :=
  zs.all fun z => (z < 1 <<< n) && !tgt.testBit z
theorem zsCheck_sound (n tgt : ℕ) (zs : List ℕ) (h : zsCheck n tgt zs = true) :
    ∀ z ∈ zs,z < 1 <<< n /\ tgt.testBit z = false := by
  intro z hz
  unfold zsCheck at h
  simp only [List.all_eq_true,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at h
  exact h z hz
def slicesSomeCheck (nSlices : ℕ) (slices : BT SliceData) : Bool :=
  (List.range nSlices).all fun ri => (btGet slices ri).isSome
theorem slicesSomeCheck_sound (nSlices : ℕ) (slices : BT SliceData)
    (h : slicesSomeCheck nSlices slices = true) :
    ∀ ri < nSlices,∃ sl,btGet slices ri = some sl := by
  intro ri hri
  unfold slicesSomeCheck at h
  simp only [List.all_eq_true,List.mem_range] at h
  have h1 := h ri hri
  cases hget : btGet slices ri with
  | none => simp [hget] at h1
  | some sl => exact ⟨sl,rfl⟩
def allLevelsOK (n tgt cap nSlices : ℕ) (zs : List ℕ) (slices : BT SliceData) (syms : BT SymData)
    (levels : Array (BT CertNode)) : Bool :=
  (List.range cap).all fun d =>
    if hd : d < levels.size then
      let nextLv := if h2 : d + 1 < levels.size then levels[d + 1] else BT.leaf none
      btAll (checkNode n tgt cap d nSlices zs slices syms nextLv) levels[d]
    else false
theorem allLevelsOK_sound (n tgt cap nSlices : ℕ) (zs : List ℕ) (slices : BT SliceData) (syms : BT SymData)
    (levels : Array (BT CertNode)) (hlen : levels.size = cap)
    (h : allLevelsOK n tgt cap nSlices zs slices syms levels = true) :
    ∀ (d : ℕ) (hd : d < cap),
      let nextLv : BT CertNode := if h : d + 1 < levels.size then levels[d + 1] else BT.leaf none
      btAll (checkNode n tgt cap d nSlices zs slices syms nextLv) (levels[d]'(by omega)) = true := by
  intro d hd nextLv
  unfold allLevelsOK at h
  simp only [List.all_eq_true,List.mem_range] at h
  have h1 := h d hd
  have hdl : d < levels.size := by omega
  simp only [hdl,↓reduceDIte] at h1
  exact h1
def bases0 : Array (ℕ × ℕ × ℕ) := #[]
theorem bases0_ok : ∀ i (hi : i < bases0.size),let (bm,bTgt,bL) := bases0[i]; ∀ s,HasSignedOn bm (maskN bm) bTgt s -> bL ≤ s := by intro i hi; simp [bases0] at hi
def tgt_K3 : ℕ := 232
def zs_K3 : List ℕ := [0,1,2,4]
def slices_K3 : BT SliceData := BT.leaf none
def syms_K3 : BT SymData := BT.leaf (some ⟨#[0,1,2],#[0,1,2],#[0,1,2,3,4,5,6,7],#[0,1,2,3,4,5,6,7],[],BT.leaf none⟩)
def levels_K3 : Array (BT CertNode) := #[
  BT.leaf (some ⟨[170,204,240],[],[],[],[1,2,4]⟩),
  BT.leaf none,
  BT.leaf none
]
theorem lb_K3 : ∀ s,HasSignedOn 3 (maskN 3) tgt_K3 s -> 4 ≤ s := by
  intro s hs
  by_contra hlt
  have hle : s ≤ 3 := by omega
  have hcap : HasSignedOn 3 (maskN 3) tgt_K3 3 := hasSignedOn_mono hle hs
  apply cert_sound 3 tgt_K3 3 0 zs_K3 bases0 slices_K3 syms_K3 levels_K3
    (by decide) (by decide)
    (by obtain ⟨z1,o1,hz1,ho1,_,_,hne⟩ := hasZeroAndOne_sound 3 (maskN 3) tgt_K3 (by decide); exact ⟨z1,o1,hz1,ho1,hne⟩)
    (allEssCheck_sound 3 tgt_K3 (by decide))
    (zsCheck_sound 3 tgt_K3 zs_K3 (by decide))
    (bases0_ok)
    (by decide +kernel)
    (slicesSomeCheck_sound 0 slices_K3 (by decide))
    (by decide +kernel)
    rfl
    (allLevelsOK_sound 3 tgt_K3 3 0 zs_K3 slices_K3 syms_K3 levels_K3 rfl (by decide +kernel))
    ⟨by decide,⟨[170,204,240],[],[],[],[1,2,4]⟩,rfl,by decide,rfl⟩
    hcap
def tgt_P4 : ℕ := 63688
def zs_P4 : List ℕ := [0,1,2,4,5,8,9,10]
def slices_P4 : BT SliceData := BT.leaf none
def syms_P4 : BT SymData := BT.leaf (some ⟨#[0,1,2,3],#[0,1,2,3],#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],BT.leaf none⟩)
def levels_P4 : Array (BT CertNode) := #[
  BT.leaf (some ⟨[43690,52428,61680,65280],[],[],[],[5,2,9]⟩),
  BT.leaf none,
  BT.leaf none
]
theorem lb_P4 : ∀ s,HasSignedOn 4 (maskN 4) tgt_P4 s -> 4 ≤ s := by
  intro s hs
  by_contra hlt
  have hle : s ≤ 3 := by omega
  have hcap : HasSignedOn 4 (maskN 4) tgt_P4 3 := hasSignedOn_mono hle hs
  apply cert_sound 4 tgt_P4 3 0 zs_P4 bases0 slices_P4 syms_P4 levels_P4
    (by decide) (by decide)
    (by obtain ⟨z1,o1,hz1,ho1,_,_,hne⟩ := hasZeroAndOne_sound 4 (maskN 4) tgt_P4 (by decide); exact ⟨z1,o1,hz1,ho1,hne⟩)
    (allEssCheck_sound 4 tgt_P4 (by decide))
    (zsCheck_sound 4 tgt_P4 zs_P4 (by decide))
    (bases0_ok)
    (by decide +kernel)
    (slicesSomeCheck_sound 0 slices_P4 (by decide))
    (by decide +kernel)
    rfl
    (allLevelsOK_sound 4 tgt_P4 3 0 zs_P4 slices_P4 syms_P4 levels_P4 rfl (by decide +kernel))
    ⟨by decide,⟨[43690,52428,61680,65280],[],[],[],[5,2,9]⟩,rfl,by decide,rfl⟩
    hcap
def bases1 : Array (ℕ × ℕ × ℕ) := #[(3,tgt_K3,4)]
theorem bases1_ok : ∀ i (hi : i < bases1.size),let (bm,bTgt,bL) := bases1[i]; ∀ s,HasSignedOn bm (maskN bm) bTgt s -> bL ≤ s := by
  intro i hi; match i with | 0 => exact lb_K3 | _ + 1 => simp [bases1] at hi
def tgt_K3pend : ℕ := 63720
def zs_K3pend : List ℕ := [0,1,2,4,8,9,10]
def slices_K3pend : BT SliceData := BT.leaf (some ⟨8,0,0,4,0,[0,1,2],255,1,[170,204,240]⟩)
def syms_K3pend : BT SymData := BT.leaf (some ⟨#[0,1,2,3],#[0,1,2,3],#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],BT.leaf (some 0)⟩)
def levels_K3pend : Array (BT CertNode) := #[
  BT.leaf (some ⟨[43690,52428,61680,65280],[],[0],[],[4,9,10,1]⟩),
  BT.leaf none,
  BT.leaf none,
  BT.leaf none
]
theorem lb_K3pend : ∀ s,HasSignedOn 4 (maskN 4) tgt_K3pend s -> 5 ≤ s := by
  intro s hs
  by_contra hlt
  have hle : s ≤ 4 := by omega
  have hcap : HasSignedOn 4 (maskN 4) tgt_K3pend 4 := hasSignedOn_mono hle hs
  apply cert_sound 4 tgt_K3pend 4 1 zs_K3pend bases1 slices_K3pend syms_K3pend levels_K3pend
    (by decide) (by decide)
    (by obtain ⟨z1,o1,hz1,ho1,_,_,hne⟩ := hasZeroAndOne_sound 4 (maskN 4) tgt_K3pend (by decide); exact ⟨z1,o1,hz1,ho1,hne⟩)
    (allEssCheck_sound 4 tgt_K3pend (by decide))
    (zsCheck_sound 4 tgt_K3pend zs_K3pend (by decide))
    (bases1_ok)
    (by decide +kernel)
    (slicesSomeCheck_sound 1 slices_K3pend (by decide))
    (by decide +kernel)
    rfl
    (allLevelsOK_sound 4 tgt_K3pend 4 1 zs_K3pend slices_K3pend syms_K3pend levels_K3pend rfl (by decide +kernel))
    ⟨by decide,⟨[43690,52428,61680,65280],[],[0],[],[4,9,10,1]⟩,rfl,by decide,rfl⟩
    hcap
def tgt_P3univ : ℕ := 65192
def zs_P3univ : List ℕ := [0,1,2,4,6,8]
def slices_P3univ : BT SliceData := BT.leaf (some ⟨2,0,0,4,0,[0,2,3],13107,1,[8738,12336,13056]⟩)
def syms_P3univ : BT SymData := BT.leaf (some ⟨#[0,1,2,3],#[0,1,2,3],#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],BT.leaf (some 0)⟩)
def levels_P3univ : Array (BT CertNode) := #[
  BT.leaf (some ⟨[43690,52428,61680,65280],[],[0],[],[1,8,6]⟩),
  BT.leaf none,
  BT.leaf none,
  BT.leaf none
]
theorem lb_P3univ : ∀ s,HasSignedOn 4 (maskN 4) tgt_P3univ s -> 5 ≤ s := by
  intro s hs
  by_contra hlt
  have hle : s ≤ 4 := by omega
  have hcap : HasSignedOn 4 (maskN 4) tgt_P3univ 4 := hasSignedOn_mono hle hs
  apply cert_sound 4 tgt_P3univ 4 1 zs_P3univ bases1 slices_P3univ syms_P3univ levels_P3univ
    (by decide) (by decide)
    (by obtain ⟨z1,o1,hz1,ho1,_,_,hne⟩ := hasZeroAndOne_sound 4 (maskN 4) tgt_P3univ (by decide); exact ⟨z1,o1,hz1,ho1,hne⟩)
    (allEssCheck_sound 4 tgt_P3univ (by decide))
    (zsCheck_sound 4 tgt_P3univ zs_P3univ (by decide))
    (bases1_ok)
    (by decide +kernel)
    (slicesSomeCheck_sound 1 slices_P3univ (by decide))
    (by decide +kernel)
    rfl
    (allLevelsOK_sound 4 tgt_P3univ 4 1 zs_P3univ slices_P3univ syms_P3univ levels_P3univ rfl (by decide +kernel))
    ⟨by decide,⟨[43690,52428,61680,65280],[],[0],[],[1,8,6]⟩,rfl,by decide,rfl⟩
    hcap
def bases4 : Array (ℕ × ℕ × ℕ) := #[(3,tgt_K3,4),(4,tgt_P4,4),(4,tgt_K3pend,5),(4,tgt_P3univ,5)]
theorem bases4_ok : ∀ i (hi : i < bases4.size),let (bm,bTgt,bL) := bases4[i]; ∀ s,HasSignedOn bm (maskN bm) bTgt s -> bL ≤ s := by
  intro i hi; match i with | 0 => exact lb_K3 | 1 => exact lb_P4 | 2 => exact lb_K3pend | 3 => exact lb_P3univ | _ + 4 => simp [bases4] at hi
def tgt_P4univ : ℕ := 4294899912
def zs_P4univ : List ℕ := [0,1,2,4,5,8,9,10,16]
def slices_P4univ : BT SliceData := BT.node (BT.node (BT.leaf (some ⟨1,0,0,5,3,[2,1,3,4],1431655765,1,[1145324612,1347440720,1426085120,1431633920]⟩)) (BT.leaf (some ⟨4,0,0,5,2,[0,1,4,3],252645135,1,[168430090,202116108,251662080,252641280]⟩))) (BT.node (BT.leaf (some ⟨2,0,0,5,2,[2,3,4,0],858993459,1,[572662306,808464432,855651072,858980352]⟩)) (BT.leaf (some ⟨8,0,0,5,3,[1,0,2,4],16711935,1,[11141290,13369548,15728880,16711680]⟩)))
def syms_P4univ : BT SymData := BT.leaf (some ⟨#[0,1,2,3,4],#[0,1,2,3,4],#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[],BT.node (BT.node (BT.leaf (some 0)) (BT.leaf (some 2))) (BT.node (BT.leaf (some 1)) (BT.leaf (some 3)))⟩)
def levels_P4univ : Array (BT CertNode) := #[
  BT.leaf (some ⟨[2863311530,3435973836,4042322160,4278255360,4294901760],[],[0,2,1,3],[],[16,5,10,9]⟩),
  BT.leaf none,
  BT.leaf none,
  BT.leaf none,
  BT.leaf none,
  BT.leaf none
]
theorem lb_P4univ : ∀ s,HasSignedOn 5 (maskN 5) tgt_P4univ s -> 7 ≤ s := by
  intro s hs
  by_contra hlt
  have hle : s ≤ 6 := by omega
  have hcap : HasSignedOn 5 (maskN 5) tgt_P4univ 6 := hasSignedOn_mono hle hs
  apply cert_sound 5 tgt_P4univ 6 4 zs_P4univ bases4 slices_P4univ syms_P4univ levels_P4univ
    (by decide) (by decide)
    (by obtain ⟨z1,o1,hz1,ho1,_,_,hne⟩ := hasZeroAndOne_sound 5 (maskN 5) tgt_P4univ (by decide); exact ⟨z1,o1,hz1,ho1,hne⟩)
    (allEssCheck_sound 5 tgt_P4univ (by decide))
    (zsCheck_sound 5 tgt_P4univ zs_P4univ (by decide))
    (bases4_ok)
    (by decide +kernel)
    (slicesSomeCheck_sound 4 slices_P4univ (by decide))
    (by decide +kernel)
    rfl
    (allLevelsOK_sound 5 tgt_P4univ 6 4 zs_P4univ slices_P4univ syms_P4univ levels_P4univ rfl (by decide +kernel))
    ⟨by decide,⟨[2863311530,3435973836,4042322160,4278255360,4294901760],[],[0,2,1,3],[],[16,5,10,9]⟩,rfl,by decide,rfl⟩
    hcap
def tgt_C5 : ℕ := 4293589192
def zs_C5 : List ℕ := [0,1,2,4,5,8,9,10,16,18,20]
def slices_C5 : BT SliceData := BT.node (BT.node (BT.node (BT.leaf (some ⟨1,0,0,4,1,[1,2,3,4],1431655765,1,[1145324612,1347440720,1426085120,1431633920]⟩)) (BT.leaf (some ⟨16,0,0,4,1,[0,1,2,3],65535,1,[43690,52428,61680,65280]⟩))) (BT.leaf (some ⟨4,0,0,4,1,[1,0,4,3],252645135,1,[168430090,202116108,251662080,252641280]⟩))) (BT.node (BT.leaf (some ⟨2,0,0,4,1,[0,4,3,2],858993459,1,[572662306,808464432,855651072,858980352]⟩)) (BT.leaf (some ⟨8,0,0,4,1,[2,1,0,4],16711935,1,[11141290,13369548,15728880,16711680]⟩)))
def syms_C5 : BT SymData := BT.leaf (some ⟨#[0,1,2,3,4],#[0,1,2,3,4],#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[],BT.node (BT.node (BT.node (BT.leaf (some 0)) (BT.leaf (some 4))) (BT.leaf (some 2))) (BT.node (BT.leaf (some 1)) (BT.leaf (some 3)))⟩)
def levels_C5 : Array (BT CertNode) := #[
  BT.leaf (some ⟨[2863311530,3435973836,4042322160,4278255360,4294901760],[],[0,1,2,3,4],[(23,0,0),(39,0,1),(55,0,2),(71,0,3),(295,0,4),(311,0,5),(327,0,6),(567,0,7),(583,0,8),(839,0,9)],[5,10,18,9,20]⟩),
  BT.node (BT.node (BT.node (BT.node (BT.leaf (some ⟨[2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[],[],[],[5,10,8,20,9]⟩)) (BT.leaf (some ⟨[2863311530,3435973836,4042322160,4278255360,4294901760,4294963440],[],[],[(848,0,8),(860,0,9)],[20,9,10,5,18]⟩))) (BT.leaf (some ⟨[2863311530,3435973836,4042322160,4244438268,4278255360,4294901760],[],[],[],[5,10,9,16,18,20]⟩))) (BT.node (BT.leaf (some ⟨[2863311530,3435973836,4042322160,4278255360,4289396650,4294901760],[],[],[(1104,0,2),(1112,0,3)],[9,18,20,5,10]⟩)) (BT.leaf (some ⟨[2863311530,3435973836,4042322160,4278255360,4294901760,4294954188],[],[],[(80,0,6),(92,0,7)],[18,5,9,10,20]⟩)))) (BT.node (BT.node (BT.node (BT.leaf (some ⟨[2863311530,3435973836,4042322160,4210752250,4278255360,4294901760],[],[],[(304,0,0),(316,0,1)],[5,10,18,9,20]⟩)) (BT.leaf (some ⟨[2863311530,3435973836,4042322160,4278255360,4294901760,4294967040],[],[],[],[9,18,2,5,10]⟩))) (BT.leaf (some ⟨[2863311530,3435973836,4042322160,4278255360,4291624908,4294901760],[],[],[(576,0,4),(588,0,5)],[10,5,20,9,18]⟩))) (BT.node (BT.leaf (some ⟨[2863311530,3435973836,4042322160,4278255360,4294901760,4294945450],[],[],[],[9,18,4,10,5,20]⟩)) (BT.leaf (some ⟨[2863311530,3435973836,4042322160,4278255360,4293984240,4294901760],[],[],[],[10,5,1,18,9]⟩)))),
  BT.node (BT.node (BT.node (BT.node (BT.leaf (some ⟨[2863311530,3368601800,4042322160,4278255360,4294901760],[],[],[],[5,8,20,9]⟩)) (BT.leaf (some ⟨[2863311530,3435973836,4042322160,4278251520,4294901760],[],[],[],[5,18,20]⟩))) (BT.leaf (some ⟨[2863311530,3435973836,4039176384,4278255360,4294901760],[],[],[],[9,18,10]⟩))) (BT.node (BT.leaf (some ⟨[2863311530,3435973836,4042322160,4278255360,4289331200],[],[],[],[5,10,9]⟩)) (BT.leaf (some ⟨[2863302792,3435973836,4042322160,4278255360,4294901760],[],[],[],[10,20,18]⟩)))) (BT.node (BT.node (BT.node (BT.leaf (some ⟨[842150450,2863311530,4042322160,4278255360,4294901760],[],[],[],[5,8,9]⟩)) (BT.leaf (some ⟨[16711920,2863311530,3435973836,4042322160,4294901760],[],[],[],[20,1,5]⟩))) (BT.leaf (some ⟨[252448524,2863311530,3435973836,4278255360,4294901760],[],[],[],[10,1,9]⟩))) (BT.node (BT.leaf (some ⟨[65450,2863311530,3435973836,4042322160,4278255360],[],[],[],[9,2,10]⟩)) (BT.leaf (some ⟨[1431651396,3435973836,4042322160,4278255360,4294901760],[],[],[],[18,4,20]⟩)))),
  BT.leaf none,
  BT.leaf none,
  BT.leaf none
]
theorem lb_C5 : ∀ s,HasSignedOn 5 (maskN 5) tgt_C5 s -> 7 ≤ s := by
  intro s hs
  by_contra hlt
  have hle : s ≤ 6 := by omega
  have hcap : HasSignedOn 5 (maskN 5) tgt_C5 6 := hasSignedOn_mono hle hs
  apply cert_sound 5 tgt_C5 6 5 zs_C5 bases4 slices_C5 syms_C5 levels_C5
    (by decide) (by decide)
    (by obtain ⟨z1,o1,hz1,ho1,_,_,hne⟩ := hasZeroAndOne_sound 5 (maskN 5) tgt_C5 (by decide); exact ⟨z1,o1,hz1,ho1,hne⟩)
    (allEssCheck_sound 5 tgt_C5 (by decide))
    (zsCheck_sound 5 tgt_C5 zs_C5 (by decide))
    (bases4_ok)
    (by decide +kernel)
    (slicesSomeCheck_sound 5 slices_C5 (by decide))
    (by decide +kernel)
    rfl
    (allLevelsOK_sound 5 tgt_C5 6 5 zs_C5 slices_C5 syms_C5 levels_C5 rfl (by decide +kernel))
    ⟨by decide,⟨[2863311530,3435973836,4042322160,4278255360,4294901760],[],[0,1,2,3,4],[(23,0,0),(39,0,1),(55,0,2),(71,0,3),(295,0,4),(311,0,5),(327,0,6),(567,0,7),(583,0,8),(839,0,9)],[5,10,18,9,20]⟩,rfl,by decide,rfl⟩
    hcap
def bases6 : Array (ℕ × ℕ × ℕ) := #[(3,tgt_K3,4),(4,tgt_P4,4),(4,tgt_K3pend,5),(4,tgt_P3univ,5),(5,tgt_P4univ,7),(5,tgt_C5,7)]
theorem bases6_ok : ∀ i (hi : i < bases6.size),let (bm,bTgt,bL) := bases6[i]; ∀ s,HasSignedOn bm (maskN bm) bTgt s -> bL ≤ s := by
  intro i hi; match i with | 0 => exact lb_K3 | 1 => exact lb_P4 | 2 => exact lb_K3pend | 3 => exact lb_P3univ | 4 => exact lb_P4univ | 5 => exact lb_C5 | _ + 6 => simp [bases6] at hi
def tgt_W5 : ℕ := 0xfffffffefefceea0
def zs_W5 : List ℕ := [0,1,2,3,4,6,8,12,16,17,24,32]
def zsArr_W5 : Array ℕ := #[0,1,2,3,4,6,8,12,16,17,24,32]
abbrev BN {α : Type} := @BT.node α
abbrev BL {α : Type} (x : α) := BT.leaf (some x)
abbrev BE {α : Type} : BT α := BT.leaf none
def slices_W5 : BT SliceData := BN (BN (BN (BN (BN (BL ⟨1,0,0,7,4,[2,4,1,3,5],0x5555555555555555,0x1,[0x4444444444444444,0x5050505050505050,0x5500550055005500,0x5555000055550000,0x5555555500000000]⟩) (BL ⟨21,0,0,4,0,[1,3,5],0x50500000505,0x1,[0x40400000404,0x50000000500,0x50500000000]⟩)) (BN (BL ⟨10,0,0,5,3,[2,0,4,5],0x33003300330033,0x1,[0x22002200220022,0x30003000300030,0x33000000330000,0x33003300000000]⟩) (BL ⟨40,0,0,4,1,[0,2,4,1],0xff00ff,0x1,[0xaa00aa,0xcc00cc,0xf000f0,0xff0000]⟩))) (BN (BN (BL ⟨5,0,0,5,3,[1,3,4,5],0x505050505050505,0x1,[0x404040404040404,0x500050005000500,0x505000005050000,0x505050500000000]⟩) (BL ⟨32,0,0,7,5,[0,2,4,1,3],0xffffffff,0x1,[0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]⟩)) (BL ⟨16,0,0,7,4,[1,3,0,2,5],0xffff0000ffff,0x1,[0xaaaa0000aaaa,0xcccc0000cccc,0xf0f00000f0f0,0xff000000ff00,0xffff00000000]⟩))) (BN (BN (BN (BL ⟨3,0,0,5,2,[2,4,5,3],0x1111111111111111,0x1,[0x1010101010101010,0x1100110011001100,0x1111000011110000,0x1111111100000000]⟩) (BL ⟨24,0,0,5,2,[0,2,5,1],0xff000000ff,0x1,[0xaa000000aa,0xcc000000cc,0xf0000000f0,0xff00000000]⟩)) (BL ⟨12,0,0,5,2,[1,4,5,0],0xf000f000f000f,0x1,[0xa000a000a000a,0xc000c000c000c,0xf0000000f0000,0xf000f00000000]⟩)) (BN (BN (BL ⟨8,0,0,7,4,[0,2,4,1,5],0xff00ff00ff00ff,0x1,[0xaa00aa00aa00aa,0xcc00cc00cc00cc,0xf000f000f000f0,0xff000000ff0000,0xff00ff00000000]⟩) (BL ⟨34,0,0,4,1,[3,0,2,4],0x33333333,0x1,[0x22222222,0x30303030,0x33003300,0x33330000]⟩)) (BL ⟨18,0,0,5,3,[0,2,3,5],0x333300003333,0x1,[0x222200002222,0x303000003030,0x330000003300,0x333300000000]⟩)))) (BN (BN (BN (BN (BL ⟨2,0,0,7,4,[3,0,2,4,5],0x3333333333333333,0x1,[0x2222222222222222,0x3030303030303030,0x3300330033003300,0x3333000033330000,0x3333333300000000]⟩) (BL ⟨22,0,0,4,0,[0,3,5],0x30300000303,0x1,[0x20200000202,0x30000000300,0x30300000000]⟩)) (BN (BL ⟨11,0,0,4,0,[2,4,5],0x11001100110011,0x1,[0x10001000100010,0x11000000110000,0x11001100000000]⟩) (BL ⟨48,0,0,4,1,[1,3,0,2],0xffff,0x1,[0xaaaa,0xcccc,0xf0f0,0xff00]⟩))) (BN (BN (BL ⟨6,0,0,5,2,[0,3,5,4],0x303030303030303,0x1,[0x202020202020202,0x300030003000300,0x303000003030000,0x303030300000000]⟩) (BL ⟨33,0,0,4,1,[2,4,1,3],0x55555555,0x1,[0x44444444,0x50505050,0x55005500,0x55550000]⟩)) (BL ⟨17,0,0,5,2,[1,3,5,2],0x555500005555,0x1,[0x444400004444,0x505000005050,0x550000005500,0x555500000000]⟩))) (BN (BN (BN (BL ⟨4,0,0,7,4,[0,3,1,4,5],0xf0f0f0f0f0f0f0f,0x1,[0xa0a0a0a0a0a0a0a,0xc0c0c0c0c0c0c0c,0xf000f000f000f00,0xf0f00000f0f0000,0xf0f0f0f00000000]⟩) (BL ⟨26,0,0,4,0,[0,2,5],0x3300000033,0x1,[0x2200000022,0x3000000030,0x3300000000]⟩)) (BL ⟨13,0,0,4,0,[1,4,5],0x5000500050005,0x1,[0x4000400040004,0x5000000050000,0x5000500000000]⟩)) (BN (BN (BL ⟨9,0,0,5,3,[4,2,1,5],0x55005500550055,0x1,[0x44004400440044,0x50005000500050,0x55000000550000,0x55005500000000]⟩) (BL ⟨36,0,0,4,1,[0,3,1,4],0xf0f0f0f,0x1,[0xa0a0a0a,0xc0c0c0c,0xf000f00,0xf0f0000]⟩)) (BL ⟨20,0,0,5,3,[3,1,0,5],0xf0f00000f0f,0x1,[0xa0a00000a0a,0xc0c00000c0c,0xf0000000f00,0xf0f00000000]⟩))))
def syms_W5 : BT SymData := BN (BN (BN (BN (BL ⟨#[0,1,2,3,4,5],#[0,1,2,3,4,5],#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],[],BN (BN (BN (BN (BN (BL 0) (BL 16)) (BN (BL 8) (BL 24))) (BN (BN (BL 4) (BL 20)) (BL 12))) (BN (BN (BN (BL 2) (BL 18)) (BL 10)) (BN (BN (BL 6) (BL 22)) (BL 14)))) (BN (BN (BN (BN (BL 1) (BL 17)) (BN (BL 9) (BL 25))) (BN (BN (BL 5) (BL 21)) (BL 13))) (BN (BN (BN (BL 3) (BL 19)) (BL 11)) (BN (BN (BL 7) (BL 23)) (BL 15))))⟩) (BL ⟨#[3,4,0,1,2,5],#[2,3,4,0,1,5],#[0,8,16,24,1,9,17,25,2,10,18,26,3,11,19,27,4,12,20,28,5,13,21,29,6,14,22,30,7,15,23,31,32,40,48,56,33,41,49,57,34,42,50,58,35,43,51,59,36,44,52,60,37,45,53,61,38,46,54,62,39,47,55,63],#[0,4,8,12,16,20,24,28,1,5,9,13,17,21,25,29,2,6,10,14,18,22,26,30,3,7,11,15,19,23,27,31,32,36,40,44,48,52,56,60,33,37,41,45,49,53,57,61,34,38,42,46,50,54,58,62,35,39,43,47,51,55,59,63],[(0xaa55aa55aa55aa55,0x5500550055005500,0xaa00aa00aa00aa,7),(0xcccc3333cccc3333,0x3333000033330000,0xcccc0000cccc,14),(0xa5a5a5a5a5a5a5a5,0x5050505050505050,0xa0a0a0a0a0a0a0a,3),(0xc3c3c3c3c3c3c3c3,0x3030303030303030,0xc0c0c0c0c0c0c0c,2)],BN (BN (BN (BN (BN (BL 3) (BL 17)) (BN (BL 7) (BL 21))) (BN (BN (BL 15) (BL 20)) (BL 1))) (BN (BN (BN (BL 10) (BL 2)) (BL 13)) (BN (BN (BL 0) (BL 24)) (BL 8)))) (BN (BN (BN (BN (BL 6) (BL 19)) (BN (BL 11) (BL 22))) (BN (BN (BL 18) (BL 23)) (BL 5))) (BN (BN (BN (BL 12) (BL 9)) (BL 16)) (BN (BN (BL 4) (BL 25)) (BL 14))))⟩)) (BL ⟨#[4,0,1,2,3,5],#[1,2,3,4,0,5],#[0,16,1,17,2,18,3,19,4,20,5,21,6,22,7,23,8,24,9,25,10,26,11,27,12,28,13,29,14,30,15,31,32,48,33,49,34,50,35,51,36,52,37,53,38,54,39,55,40,56,41,57,42,58,43,59,44,60,45,61,46,62,47,63],#[0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62,33,35,37,39,41,43,45,47,49,51,53,55,57,59,61,63],[(0xaaaa5555aaaa5555,0x5555000055550000,0xaaaa0000aaaa,15),(0x9999999999999999,0x4444444444444444,0x2222222222222222,1),(0xc3c3c3c3c3c3c3c3,0x3030303030303030,0xc0c0c0c0c0c0c0c,2),(0xf00ff00ff00ff00f,0xf000f000f000f00,0xf000f000f000f0,4)],BN (BN (BN (BN (BN (BL 1) (BL 9)) (BN (BL 15) (BL 25))) (BN (BN (BL 8) (BL 20)) (BL 0))) (BN (BN (BN (BL 5) (BL 13)) (BL 18)) (BN (BN (BL 12) (BL 23)) (BL 4)))) (BN (BN (BN (BN (BL 3) (BL 11)) (BN (BL 17) (BL 21))) (BN (BN (BL 10) (BL 22)) (BL 2))) (BN (BN (BN (BL 6) (BL 16)) (BL 19)) (BN (BN (BL 14) (BL 24)) (BL 7))))⟩)) (BN (BL ⟨#[2,3,4,0,1,5],#[3,4,0,1,2,5],#[0,4,8,12,16,20,24,28,1,5,9,13,17,21,25,29,2,6,10,14,18,22,26,30,3,7,11,15,19,23,27,31,32,36,40,44,48,52,56,60,33,37,41,45,49,53,57,61,34,38,42,46,50,54,58,62,35,39,43,47,51,55,59,63],#[0,8,16,24,1,9,17,25,2,10,18,26,3,11,19,27,4,12,20,28,5,13,21,29,6,14,22,30,7,15,23,31,32,40,48,56,33,41,49,57,34,42,50,58,35,43,51,59,36,44,52,60,37,45,53,61,38,46,54,62,39,47,55,63],[(0xa5a5a5a5a5a5a5a5,0x5050505050505050,0xa0a0a0a0a0a0a0a,3),(0xcc33cc33cc33cc33,0x3300330033003300,0xcc00cc00cc00cc,6),(0xaaaa5555aaaa5555,0x5555000055550000,0xaaaa0000aaaa,15),(0x9999999999999999,0x4444444444444444,0x2222222222222222,1)],BN (BN (BN (BN (BN (BL 6) (BL 11)) (BN (BL 14) (BL 22))) (BN (BN (BL 7) (BL 20)) (BL 3))) (BN (BN (BN (BL 18) (BL 5)) (BL 2)) (BN (BN (BL 1) (BL 25)) (BL 15)))) (BN (BN (BN (BN (BL 12) (BL 16)) (BN (BL 19) (BL 23))) (BN (BN (BL 13) (BL 24)) (BL 10))) (BN (BN (BN (BL 0) (BL 17)) (BL 9)) (BN (BN (BL 8) (BL 21)) (BL 4))))⟩) (BL ⟨#[1,2,3,4,0,5],#[4,0,1,2,3,5],#[0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62,33,35,37,39,41,43,45,47,49,51,53,55,57,59,61,63],#[0,16,1,17,2,18,3,19,4,20,5,21,6,22,7,23,8,24,9,25,10,26,11,27,12,28,13,29,14,30,15,31,32,48,33,49,34,50,35,51,36,52,37,53,38,54,39,55,40,56,41,57,42,58,43,59,44,60,45,61,46,62,47,63],[(0x9999999999999999,0x4444444444444444,0x2222222222222222,1),(0xa5a5a5a5a5a5a5a5,0x5050505050505050,0xa0a0a0a0a0a0a0a,3),(0xaa55aa55aa55aa55,0x5500550055005500,0xaa00aa00aa00aa,7),(0xaaaa5555aaaa5555,0x5555000055550000,0xaaaa0000aaaa,15)],BN (BN (BN (BN (BN (BL 12) (BL 19)) (BN (BL 4) (BL 23))) (BN (BN (BL 14) (BL 20)) (BL 6))) (BN (BN (BN (BL 13) (BL 10)) (BL 5)) (BN (BN (BL 3) (BL 21)) (BL 7)))) (BN (BN (BN (BN (BL 0) (BL 9)) (BN (BL 16) (BL 24))) (BN (BN (BL 2) (BL 25)) (BL 18))) (BN (BN (BN (BL 1) (BL 11)) (BL 17)) (BN (BN (BL 15) (BL 22)) (BL 8))))⟩))) (BN (BN (BN (BL ⟨#[0,4,3,2,1,5],#[0,4,3,2,1,5],#[0,1,16,17,8,9,24,25,4,5,20,21,12,13,28,29,2,3,18,19,10,11,26,27,6,7,22,23,14,15,30,31,32,33,48,49,40,41,56,57,36,37,52,53,44,45,60,61,34,35,50,51,42,43,58,59,38,39,54,55,46,47,62,63],#[0,1,16,17,8,9,24,25,4,5,20,21,12,13,28,29,2,3,18,19,10,11,26,27,6,7,22,23,14,15,30,31,32,33,48,49,40,41,56,57,36,37,52,53,44,45,60,61,34,35,50,51,42,43,58,59,38,39,54,55,46,47,62,63],[(0xcccc3333cccc3333,0x3333000033330000,0xcccc0000cccc,14),(0xf00ff00ff00ff00f,0xf000f000f000f00,0xf000f000f000f0,4)],BN (BN (BN (BN (BN (BL 0) (BL 9)) (BN (BL 15) (BL 23))) (BN (BN (BL 7) (BL 20)) (BL 1))) (BN (BN (BN (BL 13) (BL 5)) (BL 10)) (BN (BN (BL 3) (BL 25)) (BL 14)))) (BN (BN (BN (BN (BL 12) (BL 19)) (BN (BL 16) (BL 22))) (BN (BN (BL 18) (BL 21)) (BL 2))) (BN (BN (BN (BL 6) (BL 17)) (BL 11)) (BN (BN (BL 4) (BL 24)) (BL 8))))⟩) (BL ⟨#[3,2,1,0,4,5],#[3,2,1,0,4,5],#[0,8,4,12,2,10,6,14,1,9,5,13,3,11,7,15,16,24,20,28,18,26,22,30,17,25,21,29,19,27,23,31,32,40,36,44,34,42,38,46,33,41,37,45,35,43,39,47,48,56,52,60,50,58,54,62,49,57,53,61,51,59,55,63],#[0,8,4,12,2,10,6,14,1,9,5,13,3,11,7,15,16,24,20,28,18,26,22,30,17,25,21,29,19,27,23,31,32,40,36,44,34,42,38,46,33,41,37,45,35,43,39,47,48,56,52,60,50,58,54,62,49,57,53,61,51,59,55,63],[(0xaa55aa55aa55aa55,0x5500550055005500,0xaa00aa00aa00aa,7),(0xc3c3c3c3c3c3c3c3,0x3030303030303030,0xc0c0c0c0c0c0c0c,2)],BN (BN (BN (BN (BN (BL 6) (BL 19)) (BN (BL 4) (BL 21))) (BN (BN (BL 8) (BL 20)) (BL 12))) (BN (BN (BN (BL 10) (BL 13)) (BL 2)) (BN (BN (BL 0) (BL 23)) (BL 15)))) (BN (BN (BN (BN (BL 3) (BL 17)) (BN (BL 11) (BL 25))) (BN (BN (BL 5) (BL 24)) (BL 18))) (BN (BN (BN (BL 1) (BL 16)) (BL 9)) (BN (BN (BL 7) (BL 22)) (BL 14))))⟩)) (BL ⟨#[4,3,2,1,0,5],#[4,3,2,1,0,5],#[0,16,8,24,4,20,12,28,2,18,10,26,6,22,14,30,1,17,9,25,5,21,13,29,3,19,11,27,7,23,15,31,32,48,40,56,36,52,44,60,34,50,42,58,38,54,46,62,33,49,41,57,37,53,45,61,35,51,43,59,39,55,47,63],#[0,16,8,24,4,20,12,28,2,18,10,26,6,22,14,30,1,17,9,25,5,21,13,29,3,19,11,27,7,23,15,31,32,48,40,56,36,52,44,60,34,50,42,58,38,54,46,62,33,49,41,57,37,53,45,61,35,51,43,59,39,55,47,63],[(0xaaaa5555aaaa5555,0x5555000055550000,0xaaaa0000aaaa,15),(0xcc33cc33cc33cc33,0x3300330033003300,0xcc00cc00cc00cc,6)],BN (BN (BN (BN (BN (BL 12) (BL 16)) (BN (BL 8) (BL 22))) (BN (BN (BL 15) (BL 20)) (BL 0))) (BN (BN (BN (BL 18) (BL 2)) (BL 5)) (BN (BN (BL 1) (BL 24)) (BL 7)))) (BN (BN (BN (BN (BL 6) (BL 11)) (BN (BL 19) (BL 21))) (BN (BN (BL 10) (BL 25)) (BL 13))) (BN (BN (BN (BL 3) (BL 9)) (BL 17)) (BN (BN (BL 14) (BL 23)) (BL 4))))⟩)) (BN (BL ⟨#[2,1,0,4,3,5],#[2,1,0,4,3,5],#[0,4,2,6,1,5,3,7,16,20,18,22,17,21,19,23,8,12,10,14,9,13,11,15,24,28,26,30,25,29,27,31,32,36,34,38,33,37,35,39,48,52,50,54,49,53,51,55,40,44,42,46,41,45,43,47,56,60,58,62,57,61,59,63],#[0,4,2,6,1,5,3,7,16,20,18,22,17,21,19,23,8,12,10,14,9,13,11,15,24,28,26,30,25,29,27,31,32,36,34,38,33,37,35,39,48,52,50,54,49,53,51,55,40,44,42,46,41,45,43,47,56,60,58,62,57,61,59,63],[(0xa5a5a5a5a5a5a5a5,0x5050505050505050,0xa0a0a0a0a0a0a0a,3),(0xff0000ffff0000ff,0xff000000ff0000,0xff000000ff00,8)],BN (BN (BN (BN (BN (BL 3) (BL 11)) (BN (BL 14) (BL 25))) (BN (BN (BL 4) (BL 20)) (BL 6))) (BN (BN (BN (BL 5) (BL 18)) (BL 13)) (BN (BN (BL 12) (BL 22)) (BL 8)))) (BN (BN (BN (BN (BL 1) (BL 9)) (BN (BL 17) (BL 24))) (BN (BN (BL 2) (BL 23)) (BL 10))) (BN (BN (BN (BL 0) (BL 19)) (BL 16)) (BN (BN (BL 15) (BL 21)) (BL 7))))⟩) (BL ⟨#[1,0,4,3,2,5],#[1,0,4,3,2,5],#[0,2,1,3,16,18,17,19,8,10,9,11,24,26,25,27,4,6,5,7,20,22,21,23,12,14,13,15,28,30,29,31,32,34,33,35,48,50,49,51,40,42,41,43,56,58,57,59,36,38,37,39,52,54,53,55,44,46,45,47,60,62,61,63],#[0,2,1,3,16,18,17,19,8,10,9,11,24,26,25,27,4,6,5,7,20,22,21,23,12,14,13,15,28,30,29,31,32,34,33,35,48,50,49,51,40,42,41,43,56,58,57,59,36,38,37,39,52,54,53,55,44,46,45,47,60,62,61,63],[(0x9999999999999999,0x4444444444444444,0x2222222222222222,1),(0xf0f00f0ff0f00f0f,0xf0f00000f0f0000,0xf0f00000f0f0,12)],BN (BN (BN (BN (BN (BL 1) (BL 17)) (BN (BL 7) (BL 24))) (BN (BN (BL 14) (BL 20)) (BL 3))) (BN (BN (BN (BL 2) (BL 10)) (BL 18)) (BN (BN (BL 6) (BL 21)) (BL 4)))) (BN (BN (BN (BN (BL 0) (BL 16)) (BN (BL 9) (BL 23))) (BN (BN (BL 13) (BL 22)) (BL 5))) (BN (BN (BN (BL 12) (BL 11)) (BL 19)) (BN (BN (BL 8) (BL 25)) (BL 15))))⟩)))
def pool_W5 : Array ℕ := #[0xfffff3f2f0f0f0f0ffffcc0cffffcc00ffffffffa0a0aaa0555555555555aaaa0f0f0f0f0f0b0a0a0f0b0f0b0f0b0f0afffff0f0fff0f0f00000fdfd0000fcfcffff0202ffff02000e00ff000f00ff000f0f0f0f0f0f0ff00000105030f030f00f0f4f4f0f0f4e4eaaaaaaaaaaaaaaa8fffffff0fffff0f0eeeeeeeeeecceeccfff0eee0fff0eee0aaaaffafaaaaffaa0f030f030f030f000f0f0f0f0000f0f0ffffffff0000aa00aaaaaaaaaaaaff000f0f0f0f8a8a8a8a0f0fcfcf0a0aceceeeeeffffeeaaffaaffffffffbbbbaaaaaaaaffbbaaaaaaaaafefafefaaeeaaee0f0c0f0f0f0c0f0c0f0f00030f0f0000f0f0f3f0f0f0f3f0aaffa0f0aaaaa0a0aaffaaffaaffa0f0ffaaffffffaa0000a0a0ffffa0a0ffa0eeaaffffeeaaeeaa3f3f3f3f3a3a3a3afffffff000000000eeeeffffeeeeffee1010000010101010f0f0f0f0f4f4f4f4eeeeefefeeeeeeeefffff3f3ffff0000ffff1111ffff0000afafafafafafaaaaaaffaaffa8fca8fcfffffefefffff0f0aaaaaaaaaaaaa8a8ffffffffaafeaafeffffffff0000fefeff00ff00ff00ffaaffffffff00004444ffffffffff0fff00fafafafababababaeeeeffffaaaaaaaaececeeeeececeeeefafafafa32323232aa00ffff000000000f0fafaf00000000f0f0a0a0f0f0a0a00033333300000000fffffff2f0f0f0f0fff0fff0faf0faf00f0f0f0f0f0ff0f00000f0ff0000f0f00f0f0f0f03000f00ffffff30ffffff305f005f005f005f00fffffffff0f0a0a0ffffff0fffffff000000ffff0000ccccaaaaaaaa00002222ffffffff00cc00cc2222222222222222fffffffffaaafaaaf0f0b0b0f0f0a0a0ffccffccffccff00aaaaaaaaaaaaeeeeffff0022ffff00220f00ffff0f000f00eeeefefeeeeefefe0fff0fff00000000ff0fff00ff0fff00ffffffffaaaaeeeefffffcfcffff0000aaaaaaaaaaa0aaaaaaaaffff8888ccccfffffff0ffff0000ffffffff000000aaff0fff0fff00ff00f3f3f3f3f0f0f0f0aaaaffffaa00ff00f0f0fff0f0f0fff0fffffffffefefefefffffffffffff0f000000000fefefefeffaaffaaffaaffaa0f0f00000f0f0000cccccccccccccccc,0xffffff00fefcee00fcfcccfcfcfccccca2a2aaaaa2a2aaaa330033003300ff00ffff0000ffff0a02ffff0020ffff0022fffffffff0f0f000ffffbbb0ffffaaa0aaa0aaaaaaa2aaaaffff0a00ffff0f000f0f0f0f0f0f4e4effffaa00fcfca800ffff0302ffff03020f0f0f0f0f0f0f0effffaaaaffff0a00f0f0f0f0fff0fff0fcfcfcfcfcfca8a8f4f4f0f0f4f4f4f4ffff8888ffffaaaaffffaaaabbbbaaaa0f000f0f0f000f0afafafafaf2f2f2f2f0f0f0f030303030a0f0aaffa0a0aaaa0faf0faf0cae0caeaafaaaffaaaaaaaa0f050f050c040c040f0f03030f000300aa88aaaaaa88aa880f0a00000f0f0000ffffffffaaaaaeae00000a0f00000a0a0f5f00550f0f0000ffffffff0030003022aa000022aa22aaffffffff0c0ccccc0fff0f0f0fff0f00ffffffffff55ff00000000f3000000f0fff0fffffff0fff00303030302020202eeeee0e0eeeeeeeefffff0ffffff0000eeeeeeffeeeeeeeecfcfcfcfcfcfcecef0f0f0f0e0e0e0e0fefefefef0f0f0f0000000000000040400000000aafeaafe0000000055545554ffffaaaaffff00aaffffbbbb00000000ffffffff33003300eeeeeeeeaaaaeeeeddddddddccccccccffffffffa0a0aaaa00000000ffffcccc30f030f030f030f00f000f0f00000000aaafaaaf00000000ffffffff00ccccccffffff00ffffee00ffff0000fefe0000cccccccccc00cc000000f5f50000f0f022aaffff22aa22aafff5fff0fff5fff000000000eefeeefeeeffeeffee00ee00aaaaffffaaaaff00afafafafaeaeaeaeffffffffaaeeaaee1111555500000000eefeeefeeefeeefe0fff0fff0ccc0cccfcfcfcfcfcfcccccfffffffffffcfffcffff0f0fffff0a0aaaaaaaaaffffeeeef0f0fffff0f0f0f0a8fca8fca8fca8fcffeeffeeffeeffeeffffffffaa00ff003333333322222222aaaaaaaafefefefe00ff00ff00ee00eeffffffffffffaa00a2a2a2a2a2a0a2a0ffff0a0affff0a0a55555555555500005555555555005500aaaaffffaaaaffaafffffefeffff0000ffffeeeeffff000000330033002200220f0f0a0a0f0f0a0affffeeeeffffeeeefff0fff0fff0fff0aaaaaaaaaaaaaaaa,0xfffffffef0f0f0f0ffff00a0ffff00a2000000ff000030fcaaaa00aaaaaa22aaaa8aaaaaaa88aaaafffffffff0f000f010f0101010f010f0ffff00aaffff00a0ffffeefeffff0000ccccccccccccccc01111555511105550ffff0000ffff0022ffff00feffff0000ffffffeecccccccceecceecceecceeeeffffeeeeffffee00aaaafbfbaaaafafaaaaaffbbaaaaffaadddddddddcdcdcdca0a0f0f0a0a0f0a0fffffffff2f2f2f2f5f5f5f5f4f4f4f4eeffeeffeeaaeeaaffff3333ffff2222f0fcf0fcf0fcf0fccfcfcccccfcfccccaaeeffffaaeeaaee0f0b0f0b0f0a0f0a0f0f00050f0f00000f0f0f0f000003000f0a00000f0a0f0affffffaaffaaffaaf0f3f0f3f0f0f0f022aa33ff22aa22aaffffffffffff22aa8b8b8b8b8a8a8a8aaaaaaaaa88a888a80e0f0e0f0e0e0e0e1000100011001100fefefefefeaafeaaffffffffccff0000ffeeffffeeeeeeee0f000f050f000f00c0c0c0c0c0c0c4c40f0f0f0feeeeeeeefffefffeffaaffaa0f0f0f0f0f0e0f0e0f0f010100000000aaaaaaaf00000000ffffeeee0000eeeeaaaaaaffaa00aa00ffffffff0f0f0f00fafffafffafafafaffffffaaffffff000f0fcfcf00000000ffcfffcfffccffccffffffffffffa0a00fff0f0f00000000ffffffff000000ccafaf0f0f00000000eaeaeaeaeaeaeaea333333333333332200000000aaaaeeeeffffaaaaffaaaaaaaaaaffffaaaaeeaa0f0f000f0c0c000c1100111100000000aaaafefe00000000ffffffff44444444ffff0f0fffff0c0ccceecceecceecceeffffffa0ffffffa00e0eeeee0e0eeeee0fff0fff0aaa0aaa0f0f0f0f0f0f0e0accccffffccccccccececececeeeeeeeeaaaabbbbaaaaaaaafcf0fcf0fcf0fcf0fefefefeeeeeeeeeaaaa0000aaaaaaaaffffffff0f000f00aaffaaffaaff0000f0f00000f0f00000ff33ff00ff33ff00ffffffffececececffffff00ffddff00ffff2222ffff22220033003300300030ffffffffcc00cc00ffffaaaaffffaa000030003000300030ffffffffffccffcca0a0a0a0a0a0a0a0ffffffaaffffffaafffffffffafafafa0f0f0f0f0a0a0a0affffffff00000000,0xfffffbfaf0f0f0f08c8ccccc8c8ccc8caaaaffffa0a0fcfca2a0aaaaa2a0a2a0fbfbffff0000000000330033ccfcccfcffff0202ffff0000ffff00f0ffff00a00f0f0f0f030f020accccccccccccccaaaa00ffffa800fcfcffffceceffff0000aaaa0002aaaaaaaa00001111aaaaaaaaffffffffaa00aaaaffffa0aaffffa0a0aaaa0808aaaa0a0aaaffaabbaaffaaaaccccccccdcdcdcdc0f0f05050f0f0404ffff0000dddd0000ddddddddddddccccfafafffffafaaaaa0fcf0fcf0ace0ace0f030f030a020a02bbaaffffbbaabbaafff5ff00fff5ff000040004000440044fbfbfbfbfbfafbfaffeeffffaaaaaaaaffffddddffffcccc0f0f0f0fffccffccffffffff0f0c0f0cffffceceffffceceffffdd55ffff000055005555550055000000000000a000f0a8a8aaaaa8a8a8a8fdfdfdfdfcfcfcfcaaaaaaaaaafeaafeeeeefefe00000000ffffffff33ff0000a0a0a0aaa0a0a0a0aaaaffffaaaafefe5555555554545454ffffffccccccccccfffffffffffffafa0f0f0f0f00000e0efffefffeaaaaaaaaffffffaa0000ffaaff00ff00fff0fff0ffffff33ffffff008c8c8c8c88888888cfcccfccffccffcccc00ff00cc00ff00f0c0f0c0ffccffccffffffff22aa22aadddd0000dddd0000eeffeeff00000000fffffffff8f8f8f8faaafaaafaaafaaa33ff33ff00000000cf00cf00ce00ce00aaaaaaaaaa00ff000f030f0f0f000f000f0f0f0f0c0c0e0e00000000fefcfefcffffffff0f0f0a0affffffff0000ff00cfcfcfcfcececece0f00cf000f00cf0000005f5f000000000033002200330022fcfcf0f0fcfcf0f00fff00000fff0000ff11ff00ff11ff000000aa000000aaaafafafffffafafafaffff22aaffff22aa0e0e0e0eeeeeeeeeffffffffeaeaeaeaf0fff0f0f0fff0f0f0fff0fff0f0f0f0aaaaaaffaaaaaaaaffff00ffffff00aaffffffffffffeeeeeeeeeeee00000000ffff5555ffff0000ffffffaaffff0000ffffff00ffffcc004444444444444444aaeeaaeeaaeeaaee0f0f0f0f0f0a0f0aa2a2a2a2a2a2a2a20e0e0e0e0e0e0e0eaaaaaaaaaaa0aaa00f0f0f0f0c0c0c0cff00ff00ff00ff00,0xfff3fff2f0f0f0f0afafffff000000000f000f004e004e000f0f030b0f0f000affffaeaeffff0000ffafffaa00000000ffff0000ffffa2a2ffffffff000000a0aaa0aaa2aaa0aaa0ff00ff00ff0fff000f00ff000e00ee00ffffdddcffff0000ffff0e0effff0000ffffff00ff00ff00fffffffafffffffaffffa0f0ffffa0a0aaaaefefaaaaeeeeaaeeaaffaaeeaaeeaafaaafaaaeaaaea00000000aaaaffaa0f0f0f0f0000ff000f0f0f0faeaeaeaeeeeeffffeeeeaaaaaa220000ff330000afafefefaaaaeeeeffff88aaffff88aaffffffffffffaa220030003300300030ccffccffcceecceefafafffffafa00000f0a0f0f0f0a0f0aaaaaaaaaffffccccfafafafafac8fac8ffffcceeffffcceedd55dd55dd550000eeeeffffeeeeccccfffffffff4f4f4f410001000101010100f0f0b0b0f0f0a0a110011001000100000000000eeeefefefefcfefc00000000fafafafffafafafaaaaa0000aaaa02020000ffff0000fcfcffeeffeeff00ff00aaaaaabbaaaaaaaaffffffff0e0e0e0e000000000000000a1111111110101010ffffaaaaffffeeeeffffffffffffffaa0f00ff000000ff00aaaaffaaffaaffaa0f050f05000000000f0f0c0c0f0f0c0cdd55dd5500000000f0ff0000f0ff0000f0f0f0f0000000000f0f0f0f08080808ff000000ff000000aaaaaaaaaaa8aaa0a2a2a2a2a2a2a0a00f0f0f0f0ff00ff0aaaabbbb88888888aaaafaffaaaaaaaa00001155000000000000fcfc0000fcfcffff00ff00000000c0c0c0c0c4c4c4c4ffff00ccffff00ccffffffffeeaaeeaafffff0f0ffff0000fffefffefffefffe3f3f00003f3f0000ffff0000ffff00f0a2a2a2a2a0a0a0a0ffffaa22ffffaa223300ff003300ff00eeeeeeeee0e0e0e0ffffffff00aaaaaafff0fff0fff0ff00ffff0f00ffffff00fff0ff00fff0ff000f0f0f0f0b0b0a0aaaffaaff88cc88ccaaaaffaaaaaaffaaffffffff0f00ff00ffffccccffffcc000f0f0a0f0f0f0a0affffaa00ffffaa0000000000000000aaaaa0aaaaaaa0aaa0ffffffff0000cccc22aa22aa22aa22aa0f0f0f0f0e0e0e0e0f000f000f000f00f0f0f0f0f0f0f0f0,0xfbfbfbfaf0f0f0f0faf0fff0faf0fff00f0f0f0f0f0f00f0ffff88aaffff0000ffffccfeffff0000fffffafeffff0000a0a0aaaaa2a2aaaaffff00eeffff00000f0f0a0b0f0f0a0affff0a0affff0a00ffffaa00fefcaa000f010000ffff000000001111ffffeeeeffffff00ffff0000ffffaaaaffff8800f3f0f3f0f3f0f3f08c888c888c8c8c8ca0a0a8a8a0a0aaaaffff0f00ffff00003303330333003300aaeeaaeeaaeaaaea0f0f0f0fcecececeaaffaaffaaccaacc8acf8acf88cc88ccdcdcdcdcdcdcdcdcffafff00ffafff00eeffaaaaeeffaaaaffff3300ffff33000030003000200020fafafffffa00ff00aa8aaa8aaa88aa88ffff0f0affff0f0a0000000000003232ffffffff00002222ffffffffaeaeeeeefafafffffafaf0f0ffffffffaeaeaeaeaaaaaaaa88aa8888fafafaaaffffffaaaaafaaafaaaeaaae000000f500000000ffffffff0e0eeeee0f0f01010f0f0000ff00ff00ff10ff10fafafafafafafaaafefcfefcaa00aa00ffff00eeffff00eefafafaffaaaaaaaaaaaaaaaafffefffe1111111111110000ffffaaaa333322225555000055550000aaaa00aaaaaa0000aaffaaaaffffaaaaddccddccddccddccffffffffaa88aa88ffffffff0a0aaaaaaa00aaaaaa00aaaaaaafaaafaaaaaaaaffffffffaaaa0000a8a8a8a8a8a8a8a8ffccffccff00ff00a2a2a0a0a2a2a2a20f0f0f0f0f0fff000f0c0f0c0fcc0fccffddff00ffddff00eeeeeeeee0e00000aaa8aaa8aa00aa00fff0fff0fff0f0f0ff0fff0fff0aff0affffffffaaaafafa0f0f0f0f0c000c00fff0fff0ff00ff00aaaaaaff000000001100110011001100ffff0000ffff00aaffaaffffffaaffaaffffffff8888aaaaaeaeeeeeaeaeeeeeeeeeeeeefefefefe0000f0f00000f0f0f0f0f0f0f0f0fff00f0f00000fff0000ffff0000ffffaaaaffffa0a0ffffa2a2ffff3333ffff00000000aaaa0000aaaaffffcc00ffffcc00aaaaffffaaaafafaaaaaaaaa000000000f0a0f0a0f0a0f0aaaaaaaaaaaaa8888000000f0000000f0aaffaaffaaaaaaaafffffff0fffffff0ff55ff00ff55ff000f0f0f0f0f0f0a0affff0000ffff0000,0xf3f3f3f2f0f0f0f00000dddd0000dcdcff00ff00fe30fe30ffffaa22ffff0000ffff0500ffff0500aaaaaaaaaa88aaa8fffffff4ffff0000aaa0aaaaaaa0aaa8fffffcfeffff0000ffffaa00ffffaa02aa00ffffaa00fefcaaaaaaaaa2a2a2a0eeeeeeeeeeeceeecaaa0fff0aaa0ffa00e0eeeee0a0aaaaaf0f0fffff0f0aaaa2020f0f03030f0f0aaaaeeffaaaaeeee0f0f05050f0f0500aaaa0a0aaaaa0808ffff00aaffff00000f0f0f0f0ccc0cccaaffaaffaaffaa008caf8caf8c8c8c8caaffaaffaaafaaaaffffffffeaeaeeeeecfcecfcecfcecfcafafaaaaafafaaaaaaaabbbbaaaababa0f0f3f0f0000330000000a0000000a0affffffffaaffaaee0033003300320032ffffdddd00000000eeaaffffaaaaaaaaffaaffffffaaaaaaaeaeffffaeaeaeae0000000044044404aaa0fff0aaa0aaa0000000f0000000a0ffffffffa8fca8fca0a0a0ff000000000e0e00000f0f0000ffff0000ffffeeee0f0f00001f1f0000eeeefefe0000f0f0fbfbfbfafbfbfbfaaaaaaaffa0a0a0f00101010100000000aaaaaaa8aaaaaaa8ff00ff00ff00fff0ff00ffaaff00ffaa0fff000000ff0000ff0fff00ffffff00eaeaeeeeeaeaeeee0f0f3f3f00000000a0a0ffff00000000aa00ff00aa00ff00ffffffff00f000f0ffffffffff88ff88aaa0aaa0aaa0aaa0ff00ff00fe00fe00ffff0c00ffff0f00ffff0000ffff2222aaaaafafa0a0a0a0aaaaffffaaaaf0f0ffffffffffffffa0000010100000f0f0ffffeeaaffffeeaaeaeaeaeaeeeeeeeececececececececeffffffffffa0ffa0ffffafafffffaaaaffff0202ffff0202a0a0f0f0a0a0f0f0ff00ffffff00ffaaf0f0fcfcf0f0fcfc0f0f0f0f000c000c0f0fffff0a0aaaaafffffffffffafffaffffffffa8a8a8a800001010f0f0f0f00f000f003f003f00a8a8a8a8fcfcfcfcffffff00fff0ff00aaaaaaaa8a8a8a8aaaaaaaaaeeeeeeeefaf0faf0faf0faf0ffff000fffff0000a0a0aaaaa0a0aaaaffffffffa2a2a2a20f0f000f0f0f00000033003300000000000000ff000000aa0f0f0f0f0f0c0f0caaaaffffaaaaaaaaffffccccffffccccffffffffffff0000,0xefccefcceecceeccff55ff00ffffff000f0f0f0f0f0fff0a0f0b0f0b0f0b0a0a0f0f0f0f0f3c0f3c0f0f0f0f0f0b0f0affff0000ffff0b000f0f0a0f0f0f0a0eaaa8aaaaaaa0aaa00f00ff000e00ff00ffff0000ffff03020f0f0f0f0b0b0b0affff0000fffc0000faf0faf0faf0fff0ffffffee00000000ffffaa00ffffaa22eeaeeeaeeeaaeeaafaaaffaafaaafaaaf3f3f3f3f3f0f3f00f050f050f040f040f050f050f050f00ffff00aaffffaaaaffffcccceeeecccca0a0aaaa80808888aaffaaffaabbaaaa00000aff00000000fcf0fff0fcf0fff0aaaaaaaaa0a0a8a8aaaa8888aaaa88aafafafafafaeafaea0f0affff0f0a0f0aaaaaafafaa00af00fafafbfbfafafafa333333333300330044cc44cc44cc44ccffff5555ffff5500aaaaffffaaaaafaa0f0f0f0f0c0c0f0c1100111111001100aaaaaaffaaaaaafa1111f1f100000000cfcfffffccccccccffff0303ffff0000a0a0a0a0aaaaaaa0eeeeeeeeeeeaeeeaeeeeeeeeeee0eee00f0f000e0f0f000e0e0effff0e0e0e0eaaaaaaafaaaaaaaafffffffefffffffeaaafaaafa0a0a0a0ffffffffffff44440fff00000f0f0000aaaaeeeeeeeeeeeeffffffff88aa88aaffffffff0000fafa3030f0f03030f0f0b0b0b0b0b0b0b0b0fefcfefcfefcfefc0f0f0f0f0a0a0000aaaa8888aaaa8888ffff0f00ffff0a00a2aaa2aaa2a2a2a2f0f0f0f0b0b0b0b0aaaaafafaaaa0000a2a2f3f3a2a2a2a20000000054fc54fc0f0f0e0e0f0f0000ffffaaaacccc8888eaeaeaeafafafafafffffffff0f0fcfc0f0f0f0f0a000a00ffffffffaafaaafaaaa0aaaaaaa0aaaaaaaa00aaaaaa00aaffffafaa00000000fffffffffffffff05555555544444444fbfbfbfb00000000eeffeeffeeeeeeeeaafeaafeaafeaafefffffff0f0f0f0f0aaffaaffaaffaaaa0f0f000f00000000fffff0f0fcfcf0f0aaffaaffaafaaafaffccff00ffccff000000000000300030ffff0f0fffff0f00aaaa0a0aaaaa0a0a0f0f0f0f0f0f0000ff00ff00ee00ee00aaaaeeeeaaaaeeeeffff0f0fffff0000aaaaaaaaa8a8a8a8fefefefefefefefefffff0f0fffff0f0fffffffff0f0f0f0,0xffffef00ffffee00ffffffff55ff0000f0f0f0f0f0f0aaa00f00cf000a00ce00ffffa0b0ffffa0a0ffccff00ffddff008c8c8c8c8c8cccccffff0200ffff02020f0f0e0f0f0f0a0acc0ccc0ccc0ccc08aaaaaaaaaaa0aaa2fcfcfcf0fcfcf0f0ff00ff00ff00ee00fcfcf0f0fcfcf4f4fff3fff0fff3fff0ffffaa22ffffaa002200ff003300ff00aafaaaffaafaaafa33033303330333000000a0a00000a2a2a0a0aaaaa0a0aaa0ffff00f0fffff0f0aaaaaaaa8c8c8c8cfafaffffeaeaeeeeaaaaffffaaaabbaa0f0f0f0f080c080cffffffffececeeee0000000050005500ff33ff33ff22ff22aaaaaaaaaaaaafaaaaffaaee00000000ffff0000ffffffaaffafffaaffafffaaffffccccaaaa8888a0a0ffffa000ff00aaaaffffaaaaccccaaaaffffaaaaaeaeaaaafbfbaaaaaaaa0f000a000f0f0a0aa8a8a8a8a8aaa8aaeeeeeeee0000e0e0e0e00000eeeeeeeeaaaa0202aaaa0000fafafafafffffffacccccccccccc88880000000000005454ffffffffaaaafefeeeeeffffeeee0000eeeeeee0eeeeeee00f0f0f0e0f0f0f0ef0f0f5f0f0f0f5f0ffffbbbbffff0000ffffffffff00fff00000ffff0000aaaa0faf0faf00000000aaaaafaf00000000ff0fffffff00ff00ffffffffcccceeeefefeeeeefefeeeeeafffafffaaaaaaaaaa88aa88aa88aa88fffffefcffff0000ffffb0b0ffffa0a0f3f3f3f3f2f2f2f2fcfcfcfcf0f0f0f0ff00ff0fff00ff00000000ff000000a0000000ff000000eefcfcfcfcfcfcf0f0f0f0fffff0f000000f0f0f0f00000c0cafafffffaaaaaaaacfcccfcccfcccfccfffffcfcfffffcfc5500550055005500ffffffffdddd0000ffffaaaaff00aa00aaffaaffaa00aa00ffffffff0000ffaaffffffffaaaaffaaffffffff0000eeeeffff00ffffff00f0aaaa0000aaaa00aaaeaeaeaeaeaeaeaeaaaa0000aaaa00005555555550505050ffffffff33330000aaffaaffa0f0a0f0f4f4f4f4f4f4f4f4aaffaaff00000000ff00ffffff00ff00ffffffff888888880f0f0000ffff00000f00ff000f00ff00aaaaaaaaaaa8aaa8000000ff00000000fafafafafafafafaffffff00ffffff00,0xfef0fff0fef0fef0a2a0a2a2a2a0a2a00f0f0f0f0f0faa0a110055551100515022aa20aa22aa22aaffff0f0a00000000fffff0fff0f0f0f0aaa2aaaaaaa0aaaa0f0f0f0f0f0ffff03303330333033302aaaaaaaaaaa0aaa8ffccffc0ffccff00ffff0000ffff0002ffccff44ffccff00ffffbbaa00000000ffffaa0affffaa00aaefaaefaaeeaaeeaaffaaafaaffaaaafaaafaaafaaaffaa8c8c8c8c8c888c880f0f03030f0f0202aaaaaaaaaaaa00000f0f0f0f0fff00000000c0c000f0c0f0aaaaffffaaaaaaeeaaeeffffaaaaaaaa0f0f0f0f0c000f000f0f0f0f0a0e0a0e00000a0a00000808aaffaaffaaffaafa00000000aaffaaeeaaaaafafaaaaafaafafafefe00000000ffffccccffffeeee50f050f050f050f0fafafffffaf0fff0ffffffff222222220f0f05050c0c0404a8fca8fca8a8a8a80f0f0a0a0c0c080800000000a8fca8fcffff33ffffff00000f010f010f000f000f0f00000f0f0e0eaaaaaaaaaaaeaaaeffffffffeefeeefe00000000aaaafefecccccceeccccccee00001110000011100000010000000100ffffffff00005500ffffaeaeffffaeaeff55ff55ff5500000f0f00000f000000ff003300ff003300ffffffff00000a0abbbbffffaaaaaaaafffffffff0f0fafaeeeeeeee0000eeeeaaffffffaaaaaaaafafafafa00000000fffffcfcffffa800ffffa2a2ffffa0a0ffff0c0cffff0c000f0b0f0b000000000f00ffff0f00fff0efefffffeeeeeeeeaaaaffffaaa0fff00e0e0e0e4e4e4e4eff00fff0ff00fff00f0f0f0f000a000affffffffaaaa8888ffffa2a2ffffa2a20005000500000000ececececececececff33ff33ff30ff30ff00ff55ff00ff00fafafafaeaeaeaeafefefefefafafafaffffffff8888cccc0f0f0f000f0f0f00ccfcccfcccfcccfcaaaa0000aaaa22223333333330303030aafaaafaaafaaafaffffaaaaffffa0a0ffffffccffffffccbbbbbbbbaaaaaaaaffff0000fcfc0000ffffffffcccc00005555555555505550aaaaffff000000000000000000aa00aa0f0f0e0e0f0f0e0e0f0f0f0f0f0f0e0eaaaaaaaaa0a0a0a000000000aaaaaaaaffffaaaaffffaaaa,0xfffdff00fffcff000f0f000b0f0f000acccccccccccceeeeaaaaaaaaa2a0a2a0ffff0030ffff0000ffff0022ffff002000005d5d00005c5cefefffff00000000ff00ff00ff55aa00a2a2a2a2a2a2a2a00f0f0f0f0f0f0a0efff0ffe0fff0ff00aaaaaaaaaaa8aaaafcfcf4f4fcfcf0f0ffffaaaaffff2200ffffff00ffffaa00a0a0aaa0a0a0aaaaaaeaaaeaaafaaafa0f000f0f0f000f0c0f030f030f020f020000c0c00000c0cc0f0f0f0f0fff0f00ffff0000ffffff000f0fcfcf0f00cfcc0e0f0e0f0c0c0c0c0faf0faf0c8c0c8cbbaaffffaaaaaaaaaaaaaaaa8888a8a8aaaaafafaaaaaeaeaaaaffffaaaaffee0f0f00030000000000000a0a00000a00fffffffffafafefeffffcccc555544443333ffff00000000ff0fff0fff0fff00ffffddddffff0000ffff3030ffff3030000000f5000000f0eeffeeffeefeeefe000000ff0000000aa0a0a000ffffff000f000a000f000f000f0f000001010000aaaaaaaaaaaaaafafffffffffefcfefc0f010f01000000000f0f0f0f0f0f0f00fefefefefe00fe00fffefffe00000000ffffaaff00000000ffffffeeffffffeeffffffffffff55000f000f000c000c000f030f0300000000fafaffff00000000ffffffffeeeeaaaaffffffffff00ffaaefefefefeeeeeeee8f8f8f8f88888888eeeeeeeeaaaaaaaa0f0f0b0f0f0f0a0afff0fff0fff0aaa0a0a0f0f0b0b0f0f03333333332323232a3a3a3a3a2a2a2a2ffff0033ffff0000aaaaaaaafcfcfcfcffffaaaaffff8888ffffaaffffff0000ffffffff0a0a0a0aaaaabbbb000000002200ff002200ff00ffffffff0000fcfceeaaeeaaeeaaeeaafffffffffafaaaaaffffaa00ffffaaaaeeeeeeeeeaeaeaea0f0c0f0cffccffccffffafaaffffafaaeeeeffff00000000ffffffffffff22220f050f050f000f00eecceecceecceeccaaaafafaaaaafafaaaaaaaaa8888aaaaa8a8a8a8aaaaaaaa0f0f00005f5f00000f0f000f0f0f000affffffff00ff0000cccccccccccccc005555555500000000ffffffffffff0f00ffffffffffaaffaafffffffff0f000000000000044444444ffffffffffffaaaaffffffffcccccccc,0xeeccffcceecceeccffffaa20ffffaa22ffccffcccfcccfccffffccccffffcf00ffff0030ffff0020aa88aaaaaa8aaaaa33ff000033ff0000eeeceeeeeeeceeec000000ff0f000ff00f0f000f0f0f000e33003300ff00ff00ffffaaa0ffffa0a00f0f0f0f0f0f0f0afffffffe00000000ccccccfcccccccfcf0f0f0f0f0f0f0a0aaaafaffaaaafafafffff000ffffff000f0f000f0f0f000c0f0000000f00050000000000aaffaaaacccccccc88888888cccccccceeeeeeeeaa220000aa22aa220f0c0f0f0f000f008fcf8fcf88cc88cccc44cc44cc44cc440000000040404444aa88aa88aa88aaaa0f0f00000f0a00000f0f0f0f00000f0caa88aa88aa8aaa8a00000000fafafefeffffccccffff888855ff55ff00000000a0aaf0ffa0a0f0f00f0b0f0b0f000f00afaaffffafaaafaa0e0e00000e0e0e0e0e0e0e0e0e0e0000ffffff33ffff0000ffffffff00000e0e0f005f550f000f00ffffaaaaffff0202aaaaaaaaa8aaa8aa0f0fffff0e0eeeee0f0f0f0f000e000ef0f0f0fff0f0f0f00000111100001010fffffffffffefffeaaaaaaffaaaa0000ff50ff50ff50ff50ffff0f0f00000000f000f000f300f3000fcf0fcf00000000fffffafaffff0000aa00ffffaa00aa00eeeeffffcccccccce0e0e0e0eeeeeeeeafaf0f0faaaa0000fafafafaaaaaaaaa0f004f000f005f00ffffaaaaffffaaa0ffff0f00ffff0c00ffffffffafafaaaaf0fff0fff0ff0000fffff0f0ffffa0a03333333333332222ff55ff55ff55ff00ffffbbbbffffaaaa0f0fcfcf0000ccccaaaa8888ffffcccc0f00ffff00000000fefefefeaaaaaaaacc00cc00cc00cc000f0f0f0f0e0c0e0c5555555555555500aaaaaaaaaaffaaaacccccccc00000000ffffffffaaffaaaa0f005f000f005f00fafaaaaafafaaaaa0f0f03030f0f00000f0fffff0f00ff00ffffffff0f0f0000aaffaaffaaeeaaeeffffffff0000f0f00f000f005f005f00fffffffcffff0000ffffffff30303030ffffff00ffccff0000000000fafafafaa0a0a0a0a2a2a2a2ffffffffaa00aa00aaaaaaaaa2a2a2a200000000eeeeeeeeffffffffffffff00ffffffffaaaaaaaa,0xfdfdf0f0fcfcf0f00f00df000f00cf00fffffffff0ff00000f0f00005d5d0000aa8aaa8aaa8aaaaaffff0044ffff0000ffff22aaffff0000faf0fafafaf0faf0ffff000affff0000ffffa0a0ffffaaa0ffffaaaafcfc0000ffffcc88ffffcc00aaa8aaaaaaa8aaa800000000fffffffefffffff0fff0fff0cccccc44cccccc00aaeaaaeaaaeeaaeeff00ff00ff55ff000f0000000f050000aaaaaaaa8888cccceeaaeeaaeeaeeeae0f0f0f0f0fcc0fccffffaaaaaaffaaaaa2f3a2f3a0f0a0f00f0b0f0b0a0a0a0affff5500ffff5500aa22ffffaa22aa220f0f0f0f0c0e0c0efafafffffafafffaaaffaaffaaffaaeefafafbfbaaaaaaaa0f0a0f0a0f0a000000000a0f00000000ffffccccffff444422aa22aa22aa0000ffffffa0000000000f0a0f0f0f000f00babababababababaaaaaaaffaaaaaaeeeeeeffffeeeefefeffffccffffff0000fafafaff00000000a0a0a0ffa0a0a0a0a0a0a0a0ffffffa0aaaaffffaaaafffafafafafafafafa00eeeeeeffaaaaaaaaffffafaff0f0a0a0fefefffffefefefe00000000fffefffeffffaaaaffffffaaffffaaeeffffaaeeffffffff00000c0cffff0000ffffccccffffffff00aa00aa00000a0aaaaaaaaaa0a0ffffa0a0a0a0fafafffff0f0f0f0ffff0c0cffff0c0c0f0f0fff00000000ffff8888ffff88880f0f0f0f0b0f0a0af0f0a0f0f0f0a0a00000a0a00000b0b011005555000000000f0fafaf0c0caeaeaaa0aaa0aaa0aaaa0f000f000f000a00ff00ff00ffffff00aaffaaffaaf0aaf00faf0faf00aa00aaaaaaaeaeaaaaaeae0f0f0f0f00000a0a11001100ff00ff00aa00aa00aa00aa000f0f0f0f0f00ff00ff03ff03ff00ff00aaaaaaaaaaaaffaafafafafac8c8c8c8ffffffff0c0c0c0c0f0f5f5f000000000000cccc0000ccccffffaaffffffaaaaffffffff00000f00ffff00f0ffff00f0ffffaaaaffff22220000000054545454aaaaffffaaaaeeeeaaaaaaaa00aa00aaaaaaffffa0a0f0f00f0c0f0c0f0c0f0cff30ff30ff30ff30aaffaaaaaaffaaaaffff0000ffff0f00ffffffff0000aaaaffff00ffffff0000ffffffffeeeeeeeeffffffffff00ff00,0xfcfff0f0fcfcf0f0fcfcfcfcfcfcfc00ffffffffddddcccc0f000f00ce00ce00ffff0022ffff0000ffffffff00000a000f0f030f0f0f020affa0ffaaffa0ffa0ffffaaa0ffffaaa2ffff00aaffff0002000000ff0000fcfcffffaaa8ffffaa000f0f0e0f0f0f0e0effff0002ffff0002f3f3f3f0f3f3f3f0ffff0f00fcfc0c00fffff000fffff0f0f5f5f5f5f0f0f0f0a0a0aaaaa0a0a8a80f0f0f0fcfcccfcc5f5f00005d5d0000cccccccccccc0000ffffccccddddcccc0fcf0fcf0fcc0fcc0f0f0a0f0f0f0000aaaaaaaaa0a8a0a8aaaaaaaa8a8a8888aaeeaaffaaaaaaaa00000b0b00000a0aa0a0a0a0a0a0a2a2ff05ff00ff05ff00fafafffffafafefe0033003300000030fffff0f0f0f0f0f0afafffffaeaeeeeeffffa0ffffffa0a0f0fff0ff00000000ffffffffbabababa000000f0000000c0a8a8a8a8a8fca8fcfefeffffeeeeeeeeeeeeeeeeeeeee0e01111f1f10000f0f00f0f0000efefeeee0f0f00000e0e00000000000000005544aaafaaaf888c888c0005000400050004aaa8aaa8fffcfffc0000010100000000ffffaaaa00ff00aaffffbbaaffffbbaafffff3f3fffff0f00f000f000f000000ffffffffff00ffccaaaaafafaaaaaaaa0f3f0f3f000000000fff0f0f00ff00000f0f050500000000ff10ff10ff10ff101111333300000000ffffff00ffffcf00cccccccccccccc88ffffaaaaeeeeaaaa0f0fcfcf0f00cf0000005f5f00005f00aaa0aaa0aaa0fff0ccccfcfcccccfcfc0f0f0e0e00000000ffffffff555500000fcf0fcf00cc00ccaa88aaaaaa88aaaa0f0f0f0f000f0000ffffff00000000008c8c8c8c8c8c8c8cffffff00ff55ff00ffa0ffa0ffa0ffa0ff0fff0fff0cff0c00000000555544440f0f0f0f00000f00ffffffffffeeffeeffffaaaaffffa2a20f0000000f000f005050505050505050fffffefefffffefe0f030f030f000f00eeeeffffeeeeeeee0f000f0f0f000f00ffff00aaffff00aa0f0f0f0f0f000f0000000a0a00000a0afffcfffcfffcfffc33333333000000000f000f000f00ff00ffffa0a0ffffa0a0ffffffffa0a0a0a0ffccffccffccffcceeeeeeeeeeeeeeee,0xffffff00fffcff00ffffccccfcfcccccffffaa22ffffaa20000000ff0000f0fcffffaf00ffffaf00ffff0f0affff0000fffff3f0fffff3f00f0f4f4f000000000f005f000f004f00ffffff00ff11ff00aaaaffff0000fcfcfffffefcffffaa00ffffaafeffff0000fffffffeffff0000ffffffaacccccc880f00ffff0f00fffcffff2a2affff2222aafbaafbaafaaafa0f0f03030f0f0300ffff8888ffffccccffff00f0ffff0000aaaaaaaaaaffaa000f0f0f0f8c8c8c8c8d8d8d8d8c8c8c8caaaa0a0a888808080000000000a000aa0000000044440404aaaaeeffaaaaaaaaaaaa88aaaaaa88880f000f030f000f00ffffffffffff0022aa88aa88af8caf8cfffff5f5ffff00000055005500550000a000a000a000ff00aaaaaaaaa8a88888fbfbfbfbfbf0fbf0ffffffffffffafaaa8a8a8a8a8a8aaaaa8aaa8aaa8a8a8a80e0e0000eeeeeeee0000000000003330eefeeefe00000000ffffccccccccccccaaffaaffaafeaafe00330033003300220fef0fef00ee00ee0005000500040004fffefffeff00ff00aaaafffeaaaafffeffffffaaffffaaaaffffffffffff3300fffff0fffffff0f0eeeeeeeeaeaeaeaeeeffeeffaaaaaaaaffafffafffaaffaaffffffff04040404eeeeaaaaeeeeaaaaccccffccccccffccffffffff101010108f8f8f8f00000000fffff0f0f0fff0f0ffffff00aaaaaa000f0f0f0fcc0ccc0cf3f3f0f0f3f3f0f0aaaabbffaaaaaaaacccccc0ccccccc003333333333330000aafeaafe00000000fff0fff0fff00000ffffeeeeffffccccfefefefeccccccccfbfbfbfbaaaaaaaaaaaaaaaa000000aaaaaaaaaafafafafafffff0f0fffffff0ffffffffffffcc000000ffff0000ff00fafafafafefefefeff33ff33ff00ff00000000f0f0f0f0f0fffffffaf0f0f0f00f0f05050f0f0000aaffaaeeaaffaaeeffffffffaaa0aaa00f0000000f0f0000cccceeeecccceeeefcfcccccfcfcccccfffffafafffffafa30303030303030303300330033003300fefefefe00000000ffffaaaaffff000033333333333333000f0fffff00000000fffffffffff0fff0fffffffffcfcfcfc0f0f0f0f00000000,0xfffbfffaf0f0f0f0fcfcccccfcfcccfc0f00cf000f00df00f0fff0f0fffff0f0ffff0000ffffaa22aa88aaaaaa88aaa8fffff0f000ff00f0ffffaaa2ffffaaa0ffff000cffff0000ffffaa02ffffaa000f000f00ee00ee00ffffeeaaffffcc00ffff0300ffff030000000100ff00ff00f5f5f5f0f5f5f5f0fafafafafaf0faf0f0f0fffff0f0ff00a0a0f0a0a0a0f0f00000c0c00000c0f0aaaaaaaaaaaacccca2a2a2a2a2aaa2aaf0f0f0f0f0f0a0a0f0f0f0f0fcfcfcfcfafafffffaaaffaaeeffeeffecfcecfc0f0f0f0f0a0a0e0e0f0f0f0f0d0c0d0c0f0f03030a0a020200000a0000000f00a0a0a2a2a0a0a0a0f0f4f0f4f0f4f0f45555555555554444ffeeffffffaaffaa0505050500000000ffff0f0ffafa0a0a0000000000005f000f00ffff0f00afaaffff5f55ffff0f00ffff00ffffff00cc0e0e0f0f0e0e0e0effffeeeeeeeeeeee000000ff000000fa000000ff00000022fcfcfcfccccccccca0a0a0a0a0a0a0aaffffffffeeeefefefffcfffcff00ff00ffeeffffffeeffeeffff0e0effff0e0e000000fe000000fe0e0e0e0e2e2e2e2ef0f0f4f4f0f0f4f4ffffffffc0c0cccc0f000f00cf00cf00fafaffffaaaaaaaa0f0f030300000000fafafefefafafefef0ff00ff00000000ffffffffa0a0f0f0ffffaaa0ffffaaa0ffffc0c0ffffc0c0ff00ff00ff30ff30ffccffcceecceeccfffffff0ffffff000000a0a02222a2a20000a0ff00000000f5f5f0f0f5f5f0f0ccccccccfcfcfcfcafafafafaaaaaaaaffffff55ffffff00ffffeeeeffffaaaa00300030f0f0f0f00f0fafaf0000aaaa00000000fcfcfcfca0a0a0a0aaaaaaaa22aa22aa22a222a2ffffeeee00000000eeeeeeeeececececfbfbfbfbfafafafaaaaaffffaaaa00001111111100000000fffffffffcfc0000ffff0055ffff0000aaaa8888aaaaaaaaaaaafefeaaaafefeffff0000ffff0202ff55ff55ff00ff00ffffffaa000000000000111100000000cfcfcfcfccccccccaaaaaaaa0000aaaa000000ff000000cc0f000f00ff00ff00ffffccccffff0000aaaaaaaa88888888ffffffffffffccccffff0f00ffff0f00fcfcfcfcfcfcfcfc]
def getPW (pool : Array ℕ) (idx : ℕ) : ℕ :=
  ((pool.getD (idx &&& 15) 0) >>> ((idx >>> 4) * 64)) &&& 0xffffffffffffffff
def decW (pool : Array ℕ) (b : ℕ) : ℕ × ℕ :=
  if (b &&& 1) == 0 then
    (getPW pool ((b >>> 1) &&& 7),b >>> 4)
  else if (b &&& 2) == 0 then
    (getPW pool (8 + ((b >>> 2) &&& 63)),b >>> 8)
  else
    (getPW pool ((b >>> 2) &&& 2047),b >>> 13)
def decWs (pool : Array ℕ) : ℕ -> ℕ -> List ℕ × ℕ
  | 0,b => ([],b)
  | k + 1,b => let (w,b1) := decW pool b; let (ws,b2) := decWs pool k b1; (w :: ws,b2)
def decPaid : ℕ -> ℕ -> List (ℕ × ℕ) × ℕ
  | 0,b => ([],b)
  | k + 1,b => let (ps,b1) := decPaid k (b >>> 7); ((b &&& 31,(b >>> 5) &&& 3) :: ps,b1)
def decPrune : ℕ -> ℕ -> List ℕ × ℕ
  | 0,b => ([],b)
  | k + 1,b => let (rs,b1) := decPrune k (b >>> 5); ((b &&& 31) :: rs,b1)
def decEdges : ℕ -> ℕ -> List (ℕ × ℕ × ℕ) × ℕ
  | 0,b => ([],b)
  | k + 1,b =>
    let mc := (((b &&& 7) * 16 + ((b >>> 3) &&& 7)) * 16) + ((b >>> 6) &&& 15)
    let (es,b1) := decEdges k (b >>> 25)
    ((mc,(b >>> 10) &&& 15,(b >>> 14) &&& 2047) :: es,b1)
def decZs (zArr : Array ℕ) : ℕ -> ℕ -> List ℕ × ℕ
  | 0,b => ([],b)
  | k + 1,b => let (zs,b1) := decZs zArr k (b >>> 4); (zArr.getD (b &&& 15) 0 :: zs,b1)
def decNode (pool : Array ℕ) (zArr : Array ℕ) (b : ℕ) : CertNode × ℕ :=
  let (ws,b1) := decWs pool (5 + (b &&& 3)) (b >>> 2)
  let (zs,b2) := decZs zArr (b1 &&& 15) (b1 >>> 4)
  if (b2 &&& 1) == 0 then (⟨ws,[],[],[],zs⟩,b2 >>> 1)
  else
    let b3 := b2 >>> 1
    let (paid,b4) := if (b3 &&& 1) == 0 then ([],b3 >>> 1) else decPaid ((b3 >>> 1) &&& 31) (b3 >>> 6)
    let (prune,b5) := if (b4 &&& 1) == 0 then ([],b4 >>> 1) else decPrune ((b4 >>> 1) &&& 15) (b4 >>> 5)
    let (edges,b6) := if (b5 &&& 1) == 0 then ([],b5 >>> 1) else decEdges ((b5 >>> 1) &&& 127) (b5 >>> 8)
    (⟨ws,paid,prune,edges,zs⟩,b6)
def decBTAux (pool : Array ℕ) (zArr : Array ℕ) : ℕ -> ℕ -> BT CertNode × ℕ
  | 0,b => (BT.leaf none,b)
  | fuel + 1,b =>
    let tag := b &&& 3; let b1 := b >>> 2
    if tag == 0 then (BT.leaf none,b1)
    else if tag == 1 then let (u,b2) := decNode pool zArr b1; (BT.leaf (some u),b2)
    else let (l,b2) := decBTAux pool zArr fuel b1; let (r,b3) := decBTAux pool zArr fuel b2; (BT.node l r,b3)
def D (b : ℕ) : BT CertNode := (decBTAux pool_W5 zsArr_W5 256 b).1
def CF (d : ℕ) (nx t : BT CertNode) : Bool := btAll (checkNodeFast 6 tgt_W5 10 d 26 zs_W5 slices_W5 syms_W5 nx) t
theorem cf_nd (d : ℕ) (nx l r : BT CertNode) : CF d nx (BN l r) = (CF d nx l && CF d nx r) := rfl
theorem cf_em (d : ℕ) (nx : BT CertNode) : CF d nx BE = true := rfl
def v0 : BT CertNode := D 0x97fb0042dd801d5ec00ca760091fac0415d601c9eb00c4758024f8c013dc60049e3000c718090fa8041dd401cdea00c6750050f8802bdc40115e2006a710020f68010db40061da00046d0096fa40425d201d1e900c8748059f8402c5c20119e1006c708056f64028db20111d900686c8026f44012da2004dd1000e688092fa00405d001c1e800c0740023f800145c00045e00000700053f6002a5b00105d800626c0052f4002ada00101d00060680022f20014d900041c80002643c9a5973b64a68025
def v1_0 := D 0x12cffa0957dd04a0de824c6741242fa02315d048b1e824187411ed7608e17b0508fe628077313f37989e99cc4e8be61b457313847989b21cc4d0ed6264aeb1302f589715ac2427c6109ee305c4f1806638c5087e428037213f17909e89c84e83e41b417213867909b31c84d06d4264eea1300f509705a83e87c41fdee20e50f105883881f87b40fc6da0630ed00823684b37e2255b7112817889309c44903e208c171122e7889071c447bdd22381e91073f08838b843333c21598e10fedec87d1b64394bb21624d9084de88485b44171ba2019cd108a7f00478a800a8bc00515a01027ec0854a602d8bb01695981025e80855a402d83a016919008a5e40479a200a8390051188a9a00a64c172c54687082c110125003ba5973b60d4a680290b31fa85837d42c8fe81601f40540f60576fc82b03e402815a0146c88552ec02a166014c1b00a40980516ea028365013d9a809c0940519e80284e4013e5a009c69004d2e4026162012c19009428819c52218162c8170a5478a0e34889040c03b5973ab64a6802e99842836a2113f41060fa0820fcc4083e6104ea301a0f180c068c4007e41fc1f20fc1f887d07c40782d21901e10580e887c3ec03d93601ea3a00f24d007856603bbf201d9d900ea1c40741620c4738ca0e6b225c7850828c8b064c892203868c7e74b72ec94d0044322695750869f60495bb0182bd801c0ec1041f585d57ac2307c605d5e31013f507e8ba839abd41654ea1081f10845b883403c415c0e208cb6d01707684d02e2100fe908117483207a40481d21f8fe110097087307842c81c22096d90ba0ec8490f4421cda20c01d100ea688a85ea053b3502a8ba01524d00a63660553f202a5d901501c40a716215c7428f1414b173064895164020328ee8de56d929a008664183fea0bdaf505cefa82d63d4190fe80c41f40529f602827b01807e60bcef305c0f982d33cc1607d60b1eeb0560f582a53ac148dc60a01e304ebf90265ec81285640901f20460d902202c80ec7d40723aa036f5501a77a80cb3540618aa0421d10201a880f83440788a203abed01c5e680d85340681da0320cd01832680bb7e2059eb102aef881416c406cfd20327a9016ef480a62a4078d420385a1026dec8125a640883b204059902e7f80160ac00a83e00511b00267f40128aa008b3d00411a801e95000e46800697b0030b980160ec00a3262252101cb082a2c98e0840687220828902021d3cad9b25340a814d40b45ec0ca0f502d0768449f50220f2810ecd408604a0469f40230f201164d008a6480469730230b181166cc08a7460449720220b1010eec808614409e0b6a482a02260b992c1c80b1a242022801bcb9d2db253401085e424c7ea1201f508e0da01206b02307e61141f30880f58430fc82103e4104a620260ed0400fc41f83e20a41e907c0b083d3ec01e13600ed7a8074b9403966a01c02500de19806cfc803576401a1f100cc588351ce4b49ccf1e5c88a0a20210300c99216243868726b56ec94d0046330738fd4391bea1cc7f40e40fa02b27b038b7e61c1bb30de15986e07cc3683661b00b30d6bd586a8aac0f8b561a58ab0d65d186a1a8c0fc3461a64a30ba1f905c3ac82d9be4169db207c35100e26883437e219d2f10cc0f886543c43245d218cde90c837086307843136b2185ad90c0d2c85f07640c82b2179059088b6880b37442e9fe01702b00b60f805a46c01f45500395a80885e400b07218e0b1812287972a348870a10109202c1807e4b366ec94c83005223c5f51322fa02f17b04c83e623c1f20ce0f502f07680b0b521705a10b80cc816064453036028d7a8144cd40a59e805213402963981486cc0a34e40513b205305b524150113260b872a5880b1a242022801dd2cb9db25340122c8074fd0032be80243f30100f98079fc80303e4014fb00082d80013e8000134000cb980046cc0018e40003b203ab4c44c03490708647131e5458922086007746eb36c94d0043639aa
def v1 : BT CertNode := v1_0
def v2_0 := D 0x2d307adbc82e45cc1da6f0cd4b773665bb3b22dd417007c0f432d05204e6692d3403d80814b4a87261890b12d103795a37b64a6801119491e7dd0fd83e82f05743f4fb61f907b0fc02d87dd3733ec0f99bb95ccfaa6d67d01eb3e60b587f278cf906e47c41f23646b91f00da8f783d47b816a3db3b89ec07c4e922e27ac1e93d4ef095b3744f4a3201d51883782eac49040899641d70d6240595582420200ec5d68e6df4529a00a653a2d92b507c46202b2ad11b0095d122810608972a2da09044022300ae694edd92990601165ee82f427015a89609cc2104c54f823260419162a79c44a3cc2141a61124f288900944473c82233241114b1855ee8c4442e42219621108190882288138af05900d4a8d8956888b90161102f6973a5b7e4a680285d1ec0d98f52ec07a1b603cdf101e508805c563390524d2a41eb0526222d1b33795ba64a68020abcd4c5172b626095b142c8d899a46ab9d1a624d2cb1168658802b2c3c51955c88c0ac1742016894b14a8c80b681102b9725b3a74a64b3c01497406f8aa87765202bb24a0dd91d02ec4883742481b90ac0989733ee0b93b705c4f182e0ecc16f7460b706105b55081f9c04e6b00f42114a3224c8221c35620666f72aa94d02a0443b24c0fa925bbd4931fe94960f495f07452507d09241e80440b002275604d839ac8b0a354974c38603262c22fa5973b64a802091aada0788be83a2ec81e0075d151811acd90b2828890088e965ced91a0082c6a0ec1b5074ffa03907d01c03660dc3f106c0f883505a41a02b20cc9b0064f9003116205c7362d241729502892d064d60b5e74b72cc944ac0443354d15ff56880fab430fcda103e60c41636820d93403ec59f83625bd9a95a26ccb3e46c0b6a350331724a20b532a2c2c9911c2428202bde56e8d929a0031e526e41b3370bd81b706c01d8b8900b324878c16442204712e6b74e94d0045db98b383a29ec1e04f4ee827a0720266b62865a1223869316305030ad022ba5973b6a6802d9580a1bebee05f60206f700c17b8041b9c0105ce00067461c19a1660d4a9706645d83702f01383f28d81f844c1ffb750ff95a87fa7cc3fc3c61fdc330fe891878288415b8b5a244179660b929568241214ef52a76c1a94d00513a2281f416e05a0b600d04503d82d47f31683b98b35bcc5903e61a81731624798b09bac5783d62b876315a9718ac078c5582c62a97f2152bb90a807c82902e429c36a14c0f50a505a85206c428c1621441ed0a197685037e227d2f113c93889d07c44e39e226dc711353b48994ba44c03d225c16912cdb08959b844a03c224c161124dec8911b64484bb223e4d911cb6888d37444617e022cbb01140f808912c044055021c1e810c8d40413f601c1f300a81d805044c0575a40234b20204bc80f734406e0720304b11034640095654ca7243d48e2288693683082086af4772d880ad005352d606f96ac77ab501bd51e0de034048d468372b4cfb85a44dc2d124a04e695812b069226a45a03f4b672ec94c2d00443af0c1f25660d8997064618a360134596041b4b95682c290080d19bb2dcb2534017eca4a0befa50167d1d0ebe93f61f4a18f7850873c2821bd94089ec7402f64fcc7b27abdd13e5ce89eaf643ee3aa1c2ed50fb5e687083344f1bb9170d9c88a16c41ccf521ac5992787dc0b83ce04523601ad1a80725cc1ba4410259ae5690b1512090a0574f2b66ca294d02a05b48913be4460df22206f51083788801bb3f87dc1ea56e015aa6073c128138ac87064c80a4c3c91116115c55b2cbba1ed340118eb8105f82d836ad0d5b16b40ccba466c1d1b250e89998742a8408c42ba60cd64a0b0a22845b430995cb9d5ab25340107ec674083ee803ddf4002cba00e7db006bbd8031d6c02a3b981407cc0392e604c76b0240f581105ac0806e403c1f20026b900e0da80683d403016a259d60b2040f1c343852c44995202c20100dd6a5ced834694d0053553296ecd598366ad1db26b4df8af207c41582b2ad11b00f5a450181a5c295082c482200c02b259b3764a641802939cff61cd07b0e61b5672c3ea3940f51c90788e44fd271c1e90fc8e89c63fa0e283d07101e01934e4b49da9050f4a211980c4c90b121dbb9cdb2b22eb4012ca2637d2460be88f36b1441772a1cb3950c5dc2852ce1424b7096a5384fc59827606c13a82609a9ba84c6d9425c66a12a02509a27204b069024b2c4120c22052d55069034a8716c8bb35eb453446250379837ab6114a6802e9d5646df2b205f959827d0b803e85b1be31f15f20abee84c8d7477c2b64154dec9902f70b477363f0b9bbe85ae1606e50ac3325646b942a30c9c7bd44a949a241634d0a6266a094ef2fe4e7924e0bcbd041e60936e2fe427124e6b8bd071c5e524d2edc169432da88987546161ef10acf385640bc42a00e105c5402995a071e94c2a55661cb16a0e596905388c829c75414d92208666881308c431c1751dc14799305912908c529016551974051fa9cb95b706a5340168d02ec06783601a4510078248202c5a75a4048404811acbd1db253401255e6a5feabf3014af580037abfa2b520cadaa065ad0278368b3836b19c0b5aff05e57f1ed241816940c1a884f55457ab360bf43685f87942fb46a17d02d0be51285f05902f726817b3240bc91985f0f882f776417b0a20bd4588395c6894a84628c216614b261645a296e82e774ae94aad00433a6741918ecbc847506401e905900b4688b31525080b08815bcad1db25340117fe4a8bf7a4841bd1ba0da88d06f0320368285dbb2a31dd12196e86ec36434412a21a91104d246850c37213452906a31085d146446cb701921b021a79404734801a963057382d49184114410405224c80b54251a140ddceea5592895a0540b691e03781f013c4680da07b04b11d86f688c17b45c1b9a2805cd1102d68e83792440bc8a205a50282c28e4fb847079c23766e0e932707ac9b03ceb941d004a0cd43306d05882da4e064915a616231e9c93426413337395ab6c4a680231d2fe0e8bae0781d683a00f1851e5591e0d9b25298890283c28b08ce5d68ed92a0082fea080fb803e79c01e36e0039a70060f300242d801114c005963001891813a2e204a30854cac682c8a04f46c4f2b71c94d004363daa5aab75ad057ad122dc60c15e34481ed0300768b603d2b543d95a00ecb2c66a1969340cbcf9865c6cc32d7641960b103f3a24ea8c315695096104da095f4b36e6c94d00415b93260bf14c0aec9483763c62b31be0d99104aac8303563bc2a31980d185b5aa827ab541e96a20c6ad10be05e44d2a721e22b10d0ad88594aa425ab5269d9b034c4d419a0680d286b0690f18346ecc1a20560d0ba30681f1033eec819e1440ce8610670588336a8421ac70488340442960844a8b46414a242d10373a7b9564a68150219d93247d898c1ec4c41f526107a93007d097c1e84bc0f0079a2e5840d2414b3004b43111c2c0a06746f2b6c94d0162af401f57760f9bb406c5e00360f3cfa879ccd43cd2e61e61b302d85101381289101a558a756856b048d048240cd526acddd29a00b7643687ea1b0ab50d72fa86a06d436cfe81b06b40d60fa06a96d02f83d81a402c0c69f98629acc30cbe6180db30be0f18680fc833cbe419976a0cb2f504d05a82f06b417415a0d13f886707c43336c21941e109b2b08566d642282b2190dd10c67f80620ac03083e01811b00be0f402710602b2d201165900bd34405d462146136c9865a4131e3912454a0391204c6921898589411ee8de5500415a00a6a58a0d9ac44ec1618b600c992006428805c4ab1a50af14c12110a2d1a79743ba574a68020c5cbbf07d61683e86501ec86a759c2c07ce158366df83ab50e055bcb7bc9dd03e4e7a2ea5dc0f53825b899903c486835a476b6d1830768c102b48c62a91520d4b970d655882b28a83d117e0e8c3476c19a8d511841e88c0cd41aa6a822f83c11789a062e0ec2b306618b02b11743d08b8fc818e1a422d83a1169d908b2a4832d16214e0ba540b4eb4ba2521080b685502f837a9b574a68022991480da9105fd087abe84443b321aad19100fc88783e44381e221a0ad0a456c4861f6042c9b02144d010a764075708b40b1ecd629082c8111a815cb9dd2b25340152cd21104f43c036a8401b141e0949f024e0f11e607549b038c69820e24204e0b4d30733cbb164a11901625a180e9999d2dcbb25340106acc75c9827c164172724098b910645b73270d3679068acc8390642045b38d32e63cba25a4c8b43239627a379b564a68020bb90e8027ec80083640011b007824620acb10120c10136f2b566c94d094b029aaa
def v2_1 := D 0xe2417d06e0d638804c5c38352e181996c04d43592e61a91b30e149081372e14cb58f2ec970b20d0c8d589de8d66d929a00835643a81a3f540a0faa0406d03b035880c1b13d2cd806c12b3016609072024586408e56acdd92986008c665745d82b906c015301012909a71a24802408e965ced929a0092bf2ee41f513c0d643466c22aaf511519a80ba356902cab3641d82268b458940be568ded929a0082cf240cbb12045d81012cc08003603fc1301fc7940fd04a0281a401409181fc5880fd14405e044812c57a350299ad4c88390082503b973a5b64a68024adcd4ca1bbb652d9db286ecd920774ac433a540ed93276de59334f2b0017964a83cac969655e82b2c90fb856279c2a046c07d70181288b842a2c823408d94a6cddda52990600b4ca46fa5ac17d326fba99205d4c8a6f848417c2e8f5596a76acae8d46285da33211dd18f8de8c74674634eba31871d18b36e87402f435c13a31405d18900e8a5056449cdb21e0f550de66a887a5444141a21f4bad0f65c687705342e4d9a1c6ead0937468c44ef261ceb930c71c98516e43882f21a853918ef588af16c42d0d421385a110adac8795a6430c3321b9d590c048c9843ee0c19ef0608f3805e0bc18102e0c00070334f7018c15809846c05e82e025d1300ef15406746a02c25401291a00885ac03b2c60173ab1062a2e03081e9d6af2aa42910889a0b208d0a07e6f36abc94d02a05b2570fb12b03d89553eb4a80f5a53078d294fd29441e9048ea882346204e2910c0b2a2c50d0e3c2911208180666f4b36c9aad004a2eddbe1760bf0bc04f9e0007cee9f7c772b3e2e205f1dc30f8ef5f7477833a12775d1ddb0e8edd96c77e9bdb1f05eddf8ee6c7dd7377c0b5bbd0de9de24f449c17a77663d3ba0dc9dcc4e4b891727706393b705a9db36e2ed5b31176eb8bb470c5d04542a4c5a170634caaa86651a2d222be19176c7bc3b53ce05d82f0ed00384691500af5681c1a530aa9598740b48293464113169089a68810e8c40871520432a10d29a86d403572d48958b00424aa12c51037a7953b6090d4a6802d0a40da85196d028005813d3f309c0f984d05ac263b6412e7f10940f884979a4244bb211c15108c8d80343e6022a3103f15c0091a9c90f46a5113222c820676e74b2c87a0ad005354d4c1b36a4df935107c9a81f62d3c1b12de0c8b4e46c03d658106b2e2c290080cdcabdd1b253400daca4e10362704fb0380cd803b569024c22484068b12811d329dbcba53401177e605008d0283445411770a04b385008dc24704e13f96609c41b04e00982616ca12882509867204a269024f2c41228a203f48a462034ba10a55a11128c120572af476c1294d005d3b08017d83e0bac1e29f20e82f907017480091d92005ec8f8276ab41aa5300d108c0668458235015e797de0bc8b505460db351068ba08324d00bb4661e8a82106038882e2c416c696385528541722d0b231a379b57094a68022dd18e0fa8c607cc62835431019a1102d8862166461a3603099a81831cc09c28d488207964a10a8b20d0689048403373a9b564a68150459a9773efab3cd7d5db1baaec35d57726f8b3c17c5da3ba2ec05d175b776ba9b7b5d2d9dae84aed73a476b991bb5800bd8d704ed728176b9003b5c6159ae246cd70c5564159ab5c2351905968d7006f40b0d7a56a75929376c9028d441389a25ad154a8e16a56b0d42a3a1a159adacac86a6562b432aec5991740ac8ab146510ad220aa1915c07bc02c05e15a8560a4d1b040b15404e56a11096900a8548652453408c0f561580248444b4428d02f2957b36094a641802d23cfba0bb17d05e0ae8c547735642f9ab315ce198ad66689e362a1b92b207c95982e50cc16a23cdb88bb07c45e02e2bc99e13346e88c356815a2b30ad11901868c415c1756a482a02664c172c1c80b2a34484045003ba5973b60d4a6802908617582d37ac421dc61c81e32ac0b91523f68a89bb42102e90e46f48433b841683c2554bd92aab6c9540764a981b25482d12a20e895066a0a84b4053a39829a6cc14f4640a70f10534188319d0a64c1262ad7aa52c13ad26d1bacbd9d325340140cd22e05f83d036a8b41b1458094a2b0664fd2a707797303aead81cb04c0df83304795081779574c28cf2e0c811641140f0a2da181499dc1d4adbba534010c98ebac078dd583c25f8dd10782da920a80887202c6890808a004ee7572ac817b680250387dc01b3ce00d3b70005d3803279800d66c006326001631000028809d13110165471926b1a09220902ba3795b6094a68021b1ed54d941b26c93d836376c0192a1013148c41034b8a0acd711120c12140be56adcd929a008bef278a3ec3c20f61e01facef83d67783ea3ba0f51dc5fa0ed83d07693603b20b007405205e6b8248103c29622384025a8c98b202420140fde696d529a03b565400fa2af02d1570068a801ec55a3f9aac1dcd5583e61441735540f5aa94d8c51cac6aa17f254e0f92a60da95283d4a9016a546bb11070588b54bb4a89bf1542dd8aa007c54fb962a7a76953a954a9c07a54dc352a68169533094a035a44264b22a60bf052ed7829607c14a89e0a502e85260f42923d81489dc0a401e01260b028f4b614703b0a356d05180e82229b20170390beca4e215921e58c8d528870c684c8a16f2a774b8872d00530597757ca0fa93305d61c03e864d5ec86e0f9c020bc9ee03e4e262ea5daaf53815b897f83c48b96da19a0ed2118aa453ab52e4d2a154cad0b9a5a654f2b328a43d143f3488be07444d2b230d89a08660cc1ad60b2028d32592a34460b95202c22028dd669ced8369a008664753f783a42bc1d00de0e702f0733d683941b41c875d8e376ec7147743841ba1c06d90ac16e42f8b322511b80ca8d80fc08928820791201048504850237659b364a67d81502da97f2feab841f55520da2a306c5831f60c149b0608cd407c16938161080b121d01b873ab9574a68020ebcaf80684d0032321cfa090c4d04858e42423b201a9152005981aacb3348b14a22841033a7359b64a6802225c9530ef8a3157c48c1be23605f08f06f4479b785a0bb82ce59c16626e0b29270590b302c64d816214c0b0b6505801282c33901603480af962057891027549a3481a447b30eb130a643518940cca5ee950069a00ba769222fd890c1ec4841f524197a9214fd29041e92bc6e887c2662080d3048a8d10288130c1010066e752b6c81d3680252f92ed3b107816c83a00f38d1c928831104c8941c24282029e94ee5d9027ed004a0a01b204e08882676c012ba60091d28046e900222c403e29288206ad143d391121412140ae69ecd5298740ba66a99bc6fa49017d1206d63369eed9ace76cd25bb21109db1f96cd86af564145ab6185918a3348d99bb74145d3a554ed90466489994ef2b3c1795ff3b8aec05c5461ac237815954a8d82a444c0252b50670a256303530a0e55834122d1a0574b276ec2294c83005a4d01be26609f0a704f46faae81a016c22219990300cc6f82e40de26a14ea9c8373e84342b226c017035e2981ad04a0d713406b9d9035aa8412ae30a0163d184325459120d102b75a3b96405a680219d937c7d89b8dec4de3f5a6e07acb293c69b5be94d80f4825754412a310271488605902e2ca8a1a1c785222410300ed65ceada569a0095f93ef8fc567c5cc0be3f061f1f7bee8fb86747dacba3d761d1f60f76fac77b7d439db3405edf49176fa083b7ce3b9be605cdf28ed6f9016b7c61bd3e289e8c582f4f84c7a7c01b93df89c9ef02e4f74c727b81b53db05a89036e247db317ace18b841a6599c3328f169130b0c8bda3ee1db1ef0ed4f3846b1500b25681d32530aad598754b48296464119cd102291885d4d45402d82d48acb092a09a2056f4b276ca21a94d005a1f01b50f60da07a0fcc3c83e61e03f10ee0f887605a42f02c21d59b00e8b9007336605c738192603895ab058f14488a3264033b3a5b976401a802319a9490368b383f359a0f9a9256c9661f60b2c9b00568cc079669425321222829312211cb9dd2b25340107ce61783eaf141f31840cd0bc06c4cbb352bbc1997828d819546a04634724a20bcb152645a0e1214101574eb366c94d002db2923a1f591d7bac8e03d646d4eb2311d51178ca88b335445412a23419111934888c2f3445d71a22c6cd11574685b0a222d9110214d0404a45ccd5b05ac52a112d01206e874b72ee94d02cf029a4369de21a4cf10c836886013442e1bd88305ed09944420419a42c7dc2153ce10a3b706edd384027981f426c0f9926077d72838e09419a9660e13e206e8510291d26932cb910a20c23684c4a6570e756ac1294d00463ae6813e0800d639904c5cc0352dcd5386c4ad431554203d518532f63cb83642889068647ac56742b36ee94d0043243a021bb300e0d980646c01e0921c797064048436b2f66a94c94f8029aaa
def v2_2 := D 0x38406f42e027ae0c1b57049be2d405f1c0a6e8e001746fe1ddb7e0cec1b0346df437a24a0bd05704a54683422481916f87dc37b3ce1bd0b70cfc5386d24d835f2681ac3f20d45d9069618433e5420cdd45c1ac03d1b152642325cd05901ab10377359b50d4a680221d4040b995c078d0082e48009a13fe0cc9fe0644fe82e07f01e01000e81500520567164a0ea022ac7a7445469322309101cd103b89735ab74a6800d394cae01bc1980b129e54e55c02c0acc120568e8c2b776415b2a10230594940351172a4058508d10278953b764a64180219d8a71be33415f2103ee8f985748a43bd9a905ee288ee71401738703b5c2515ad8b86e4c583328966194370daa1102d483069a3504cd44f6de62734f262c17989ae3cc1d6dc60184e2f781717b2e38c4c3ee2161ef10acf384611500a85681d42530a9d598752b482a04641194d102751884982ea4a01a88b901654234408d60a5cedda43529a00b47e077c3ec1be12a0de8ad06f07d03763e4bb81f0adc02b54c03e82500f0d201eea880bce2b1a47a41440926584c88b46bede56950069a0082afb53238fd19146e8c84df42102ba3208fb18fb3d8c8c7f36443b9b2107cc8442e6c807eb63f2f596b278d8b87e4c583b262a1b92b80fa9591bd481069a0a44cd31e6fc58eb6e2c71af1636d38b1a07c46b82e2c650f1630838b006fa579a5d2b891e95bc874ad48b8567b3c2b506d959f2eca235b44179ba2c5cff062c7d83153dc15c1fd0ac81e840915005256811197900bc1c85f82c804a2525ca9016110235a2973b7694a6802929275e12606f0bf9e605f8d302fa79417c34a0bd9e405e8da02f26901782c60bbba305d8b102ea2880dd2092904079746598a14e2da10129420240ee6dce9592987600842fb2501ed127836808812c044e91a4e3ec12683601ac1cd645994c3828a2e3019316117d2c9bdb253401048e4bc02d8ecc9a005a2a3022c58366b592c282889008bdce96e5929a0082c721101be086fde84206f42083781003bb07e0dd83e3ee01ecb700ad528078c900ac4ab22418f264852c204428b08bdaad65d92895a008876a9a6cfe4d301f26960d896e0645a51760d241b06905883470641a30a2026c591c0599464c929449c68c16107206eb2e756c94d00421b937effa9be07d4de83686f0fb13760d882b16a4dd23601f51a81162d2732c8123034988582c4870cbd926de8dd29a005a65327f05d13f3ae49f81712d00e8a7d26813e3b209f01880f9ad8a196848921c3498b182818568117d2cb9db2534016ccc168dd60a83eb05017582657a41207d106add86b01ec790759bb607cdda836685c3e33100f1ba78aa9560354e503e25600f12270d685c02b4f242f177a0f8a3a8ba4c883d2e34fe16fa970b3707854481c2e7d6d95c00eca360d4512cda23001d11680a8bc776c19aa5510441e8820cd440f0f82071740639ea081a0f040c26820581404801d81786cc11f0560a83b210283c88121c42e96a2204039101c58880ca4434c681b25728665c2a25245a212cbc56a4eddd29a008b64603efa1c5d7d17e1bd82f05ec5f06e62f41731760dd0bc04e85d83642e99aa1720cd0b86ce4438b621845991047d406f46a01f97300a519825255b44840f2cb92900410a8d682508066f4b366c1a94d02a05b52df6af96f037cb74b305b8cd82db64c16c1e50b5c1285b47902d964816d1630b65d185b05882d714406e8e4c04069962b19a11ad17092009033943ba56439a680210bebc407d46083590c81b1868cd846a66a02e9232d206950e4d8225ad090616250339573ba64a6802139c94c7fd4a5b5ea529df5292e7a94c0fcca59de65281f32920799480faca43dd651c1eb28c07586c0668363b522f01b028abd414466a0a2c730510d9827488074ab4a9662cd82b120902fa85973b74a68028d9a4551bea2305f514c6ea8a017544e99e22606d03c83588801ab44a1bd08305e84102b4540f381770dc0bc84e0fe9e607e49b03f04981dd5ca0eb335072812818648c1be7640b6f47956469820c888a0699417683c28b08ee4e96ddb929a008c75d503e8e801ec7520f9b9a0dadcb03d6e5416b426751844078c1d8346ea01f27261b538f07a9c702d4e9c37174c0f885c05c5c183d2b581e12e80e8ba53ec1af1340ad25986a6ec83411620c671cca0e6d1932ea918f2644c9220386b418de8de56db11a0088640c8aea0641720300b881766a00bbb200581880d8c12f30cb424c91310448091e1818568119d2c9bdb253401110e6aa6c4ffab6107d5b007e6d7c1f36bc0d90540669ae9f62d701b1056cd4ad10665ada3600f11a81983125105a587131a4482c12141015ef2b746c94d0015f293b00da9d71fd0eb03e8755bf23a80f91d33ec4e903620ac5a12b4ec89d13ec0e8236073d1a02b28c80da4d07358d2464787164c8894c4070d18de94ede5929a002e65327704e52626629081314d2b90a59048535af329917194ba0cca555465459330a289081782882a540f46a19184c4050444d0aa06746f2b6c94d0045f319d8263bd12805e84c8ab50d433953a28c8c606461a2670ac8db856609c43304c21946310c5d188609c842f76407457a416403cab14a88b94202c220564b2e76dc94d0048ba37dff51bc6fa8df4fd06f03e83749ec1b89f98db4ecc6d05e63642b31b00f98d706cc6b01e63540b31a8f758d37aac691bd6344dab1a89718d34a8c6903c63441a31981f90c43ac85c9be424ddb20ec35104d26886737e23152b11740f88ab16c4661fe03102b01720f809346c03b45501355a84b5c6092144f1644809081411f65b97364a67d8029a9819f60c081b00a028803cd620256a10e9098b04811caa539dba53401258e515bdd832c1ec86c0b9a400f8cd303c6e622ea56e0f53866f89c88dc4ce41e25172712105b68d703b4479ea99060f48bc16a6411fc3204fa1900950c7f07857c8b431f88a18fab4cc7c07659d83331ed3d18f49c8c799a463c03a26841918ee848a2c8aa064a350e88fe07469502f707817b2340e216986748cc21d2f411fcd2067c1d033c8c82bd60da257323260b9666c56152034a37957ba364a68079292a53df12206f851037a5741bc0ec09a05e04b0470372570fb82b62dc15a14c0ac82502f05a4e6593404880b121d3237b35a96405a680231da40c0d5a2905e8daab527a03213a2a909c306452013508fc91847c4c823d2420557141414b062417222a1059150150342c85bd4adb9b253401073c674bb0358b60162760cd43af76402634795646b220cd4a6225078516117cab9dd325340105fe4098272084108055c69502c7841645a15407e8de56d929a0086c633b54ca01bd594135abe05ad9402d0acd12856cc903313e61981b30ad8510139d1274a6041626d049f95ab7364a5568020ade9ac8df490bafa235dac358bbd92105ec4682c66ad7ba354b9d1a926e88402745597322644d913124c86f3b5445032220e6910de0668d40b7214853914c2d88a514c41b4f521319210cf0cc9a846e02922702991b014a89806756a0261a400d8b983fa4d69081a20b2d0e55325684c5894281bd2cb9db08a5340a816c9ae3f54d40faa693ec53403625841a94ce9d826616c132b35022e584092c14118241982d1c2c0a0674e6b72c94d005632f6417d7b00babd705ed4a83542c419a7ac09c88904448f1e70f54fa87a8cd43d32e61e91b30f44b1016e2880eb4964880d628571568b5216120902f495a7b37094a6802ddd0e45de07106f0373b761c97ba0e26dd02b04883837721bc5b90dc8dc09c52518820790084448546080a04f2f4b66c94c3b02a05b52ca0ef564837aa441bc5900dda9156e963a770b191b80568941cf6480e78a202b12a469142098b22144a3476e694ac94aad00418bd7ce0bec5105f21302e916223b62e0bdb1604ee1202e708c1336fe1d5a8802ae0204f4f8017a4361ad1840568550352aa01a15440ccaa104645003231280308cacd4464268159033118df908c4ec84455020d60ba552890042e405b42a8e1cea56dc3529a008a748a036844c3b0224ad803cd683996a90a0262c4074c8e965ecd929a008baf3484c1b44250d882ad3238165498b12483803eb476f0c94d005e316bcb978cf5cb036ae541357289be04205f01f8346cb4f385650dc2b354e1ba9e60dc89b06e249836126815a12303b7a2a3023429916b01b21e5da0a22402371a79b56e4a680221d00a0da8048ec001b3600e68c0892e3c1920c448044674b6f2c94d0045cf9aaa
def v2_3 := D 0x71e0dab8e04d5c686f24941790b00b48910545c61f70e2cf38714edc34f74e1bc9e60db49b06d84983577c41a70a20d303886882c411b6938b98d2e8c2a132a56b4264472c672742f6ae1294d00443a83637d2440bea0c06f102027882c1b441409a07706b047035280c1214127dc2083ce1038b706c85384047981ef26c0f712607857283a8cd41c504a0dc9e106c55082ba41693980f2e8c21864d080b121d320670f34a76e1a94d00463b2c24ef1608578b001bc57e05e2be6eed5e8376a41dba57895cabb16e54823702ab140a303420b04402a3407d5a6dcd9299f50600b60f06faf7c17d13e0d64580ce5591370acc5386e4cd837164c22baf511599a8862c900bb6985a40d2acc3ad6860589409d6a4ded84529a0082cfa419ff520aefa9092ed08403683449ac20e6d99060fc88283e44115ea1a20b10a316c451a3603335a4405880e4c5890480fa52dcb9ba5111da00a6a6021f92f44bc97183e4b7c0f25660d832b4e419523201f0590092a5d8a94a40584409d89661cee129a00835f252c2bc2500de09916ec580b743901a11880908621444cd1b706653203306d01973480cb26206545101ba41252080f629d08b68404a5080902f9873b564a61d80245d92ebfea9701f54b69d925a06c8b11354964bb04b08d816046a045cb105214b180e483111c2c1015f4f366a94d05eb0297961beaf305f5e502eaf2437b2500bda9416a8580b34f2033918e2d4ab50664440a22f1d338176edc0bc04e1e32f50f159a87891cc3c33661e12620f0451029692d44880f4a558ae42b521628241206744f2a76e1294d0048ba1701b50b69fa05a07d01a83461643f20b00f905706c42b03221541b00a84d00537e405e728018b0888719169548d264882018de56adcd9015a008866a9accfe4d601f20a60ad35706c5ab1f60d545b06a8ec807b56328165c229588868b061502ba37b9564a680210fc9c37fd4cd3bea70c3f33340f993e5ec85e03640ad9aa0560cd0c316c4398b3230d1b00e68d40cc1a92840d2c2c2151c0899120344850201dd3cad9b25340a814c9c813a4c4b9925204c92806449181224c4108a525445419220231a59625a30a8591814988b42c2d13373a95b64a6802f790cec2207d61481eb0a0cb585003ac2700d61347e9094df483eff64147db1f20bd84c4d6c83e9f9c144dcdf243e64c417384c3f5c2507acc913c70903ea8461d542207aa109954e39ea25484d120a1a685293350727f1802778bdb37c5ec21e3071be9802174bdb07a5ec39d2e022e15d8cf0b801b65764bb2861b51450b688bd37444bbaa3090ff08467d842207c210816082a2a014aad038e4a61522b30e54b5072ab4829a46414d3aa0a649104505e42189a205e839025d18877a416402d399305cb2f52558a34a88a1016110475973b5e0da680291940de0ce06b03803563341791980b0840596431aaa232c9a81940b00bc348061ba303245101902c40dc545a116a110b2e581911415a045f526f6ac94c3b00433b52f40af979837ca501bd5282dd2bc06c4628262bc99b85e2d982f066c177b2602b4726020359ac4235a2e12401205692b476c8734d0048ba8b53ec1900f63a40fad7a83d6e1e7ea67a0f51a7076a3a1fd31ccfa98e5154c7107a4d0b3531c04a962a350c6f0785598b431b96998da0ecb3b3666364d231ac1d135e0c8a3e3fa10f45506701e83368d43994a815b2340e496986708cc20f9a40d6a3208355a4f45b23298c172ccca8b121ca33a59b7364a680f52927a0df0fc09cc711ae60e826b0da6b18fc39c47102e21b416907473093d05c05e12603241281926901588e60ab9b305607882ae0c411ce855e9cc98244da1f5397ba6401a680281da46d1ba23507d03e02e88d01ec4660f9a2607ad1083c68c81f243e1b521907a90c02d42141da4621b8a3007c50202e28443694160f4a0a05a4ae83c28bcfb03b0cd01cc3480619b306f5d9036c2c419cf125a4f4344baf4628425266090b121da06766f34b6c22950046325e59aa5b60cd17546a16ba330131a3925105e54991283848504053d2cdb9b253425ac0a4072a7807552005c522859da6480a4c3d618684540b4ece5ce96d92992a700433b553157dd1ba03e8acd9746e6fb637207b1b882d8dc13736de0f9b4f95cdb726d6db41eb6d80b5b6b0dc9b503e4cfcd726d20f517297682ac322da0f706ce0f835c05c1b303d0848f6007a2f003305816903a06b38d989288313239688604c896582428202de8dd66dbc529a00a4f41f6279c1b10e80889e65ec0f283607913283c609407c12408162cb13228d6821c20809080503b5a379b64a6802ed99590376acc13b5640d9ab10ce94e3b64a69d32560dbc82c05e45c82b2880b880528c40bd45482c60797129421504d080b46017acbd9a86a5320c016bb807c84d82b50a81b13000c8c2e06c2138261100f2887e09443e3c821eb240ab9d188785c843b2c421d03210e45101f1520b201abd2b146554a75a89a10161103b63795ba74a68028591e2bfa8f007d47787e63b81f315c0d909606c43303523b63b01d8ed80eb66a01583300c9508192c12202c21166b82901209027a59b3764a6802ad9a98707e4c341f20920ad30c06c585af60c281b06129883087641838a2026d592205b352893ac1a2c21140adcead65929a0083ef25b07be2d60df16a06f46e82e85a9dbb2a8bdd1470ae8922b744700ba2d23190e505c8689a644386a2208ad109086e4244342114519120adc04544a0242b405225c603081ea49a21644823428138d5bcab21ed340a816c9213b248e0d92466ec5228b6213148c405852a348890608023975ab364a682f38149790564bba3100b482ca4596223c194202c2844eaf3746c94c96f8029060dde02f06f0173b760b63ba0580dd02b0488150b720a51b8118246102c28404404a342011bb2cd9b25320c0a816d52ed05f990037a37d5b561c93510605a9532a7212d59167acd833c05a19d9250ce9920672ec833854206e095d00b4a60a90522da204712b566ee94c2d00433a6d81b336adf91b407c8d99f626c81b12b40c89b146c03cb05906b125c290161019f4a3b57974a6801b394c9e63744f06fa25a65d13bc6d89d8dec4ea6b62791dcd3c03e696a5734ee3b5a7607ad3a82d65989e34e8db8a7307c52382e29c9b694e20f4a7005a4133aa20991882bac522181a40b8b143438f0a54889040c03b5973ab6954a680297780fabf907ccc30334f1d1b07f0dd43f756a1fb1f30fd4f187e90cc3f3246056912a44169660b572b48cd434629448242eea55ced929a00a26442837a210bbc1060de08206ec408374200fb80fe8dc07e44c015a2401cc9180fa2880bc4a922508a0621313169c88512119db9d2aa530ec0118ed4b403bd59e0de90406d5461b78120db45a13ddacf96ec82236634412b51cedd28e86e54623701211b01b8ac694b066445a3126ed690a5ce1295590600b5e303e90c01f27840d89960645e383611a49a08d05884677642330a20269a3250701e5558f26451271aa5a0c24407207eb2e774c94d0041ff9260ffa12f7dd0972de84b5674258efa0d765d095b1e84a9874252ff61286bb093b3d84998ec2763f993a1ecc9c8ee64e073326e0f990805cc9b11664d48332683f59331dac9913d64c496b2449f1921278c9807e44bc37225d17912d89c89603e435c17225667912a31c89487d44a0eea24e6f512633a89287c4495ee2248af11235388910db44865da240df891f6ec48f36e2329be9176ef48429f84163bc21706990a30cc8836f443e2d221c4dd10d50c89203fc08f9f60478f701947f40bb07a0419fc01f22a00e2cf006a56802e25301455980845e802c0742352201d5962a24120374f2a76ca294d0053487c13d43c094a1d0684fab270781b303912981c396810e32102239a698419e5d82a228c98968604265ee7356ac94d00417731d7400dab9f0dec2102f6104163070091b9e0de56a02f2e243717000b885a05a54782c2e74fb873879c39b26e1ae1270d989b06cb19035b6481792b30d0858829a4d8b49914991ad24d09ac16ae4d6add84529a00887405836a029fb00122d803cc30124b0e260480236e756b2c94d0045d39aaa
def v2 : BT CertNode := BN (BN (v2_0) (v2_1)) (BN (v2_2) (v2_3))
def v3_0 := D 0x1b9973cdca01e6e488ede18276f3411adc719c06d46543c39daaa8a5340114ea914ac0ba84548b805dce96d529a0142e3333208c800b3440040120b0e18458654202c03801e0494eddd29906008b751724468b8f280548c589175316e6ae941b767d802dac66a9ce42046320822190110809a08a86a221f2f0b66c94d0015f219d6ea1dab532ad56d836ab080b52b72da15536cc35aa1a523d00d148c49b297ba5401d568029a73835406d5d8095a2cb2026e74b36c94d0a530b19ec80da3c8058fc64552fc59a966c330a101887c5af33e29699b3a6ccf893265f7a3502f3b24eccb091f2af746c94d0032f29188dd98c302cc614556304dab180bd90bf82c85f40642f436a1787550bb06a85d02d42e412a170db885b05c45bced22d816916b3ac86405645836a22ac1511685b80ac05c05996c01e816012c5a80580540d5523412b222b1e4c8c354493105eb2f74b88024b0053540ec123ce479863104801d8324b05c1ad3db608a340110ea89808206b45241141406e8de6d5929a0540897353584a40dd92ac83507192ea83674d3b8872d005a6341332e208d0c00464daa860124054e882202a4ca26d4d83529a0540a768b18b0f530a76ee12b4a680219d59eb9e81c6e5225c5b0b9dab2ca5340116ed290134032f9c48b7cc24012600349288bce9006bc75190f1ef156abc87b4c0463a51c11a0388c8873179b569d4a68022dd5085a8105cc2b9db06a53401182f6aad30cba68875b34c1ae5a2016a096a495081ab44a42a8501b5a973b60d1a53401493111c491043e5d68ed894e94d005355c7cf6adb07b57133cab721e0166cec0a0674050f380f2ca56e6c1434a641802d1ce09102274607b8a200f1508090d047435110f8439b564a6815022ddac064d0602162016282d04b22a02d4445e8dee55929a00957f299493068c0943453481a212201331c0662de50ee990069a008327b49604aa4a82531a013098478842704421322101a6816310172f0b566e94d00f2463ba381ea03a41692900fa8405a94a1201f975a3b64a802157a84f04f8270262108121036a8404a98515305a8d5b2a512b010c90ed5033048c4f0253434121c64c905f754202d635ac858f4a197b6110da680221d5fa0d91e606c45f02326791b032e8983ba94a1dc9a40ee0b081182462081b3d2a716b4210530d14140cdda6e95929a05421660816a241402d509cc2b9db29ac3529a00b6579d461001a37ea0b4e6d79668480b249c9a0034acc7be7643de8711ef0588159e4accc8b3a15b9774a68020cdc92404ec91827408811924428892144e07ba2101b4100f511201e912b66c94d02a01a72daac21e70065e5296d829694d00433aa30bb05185d428b2ca01e0449d0072010497937a5b61bda534014d23e2ab7042d5c8d05c82a2eb406815a702ad448c46403dc34d0416ae8625a02426d4e9cae5d298cf70053c70199d8728402a6a23892a087d1ac4bdba53410f1e26549c0015d426410212eb2f476d8897368029aaa
def v3_1 := D 0x37c02727c4111dfe79c68f04e37f16207d85100d00d4c0162e5566c1294d0057ba3f55910382c9502c80b08550171973a5b7d1a6802199820146905002c326ac76ea94c4fb41802d4f819d99204c86882722d41294f719c27064e13702501e2894822223c69e6d7129a00ab769d582b5931d900582ea2201a40595441101b8379ab574a6802373c8852840a2e5d6e8d929a09062a05b007144403c2100b58a4620342952225182407e55e8ed826569a00a7ce93400758aca4a05e558ab4a91a413f30b566ee94d004b4f918ce940ef74806312303bc91009514a2c88a0a4e9ced55289587408676a9da0b6206da2d2c3b56b4162560736af4772c94d00b172955c199c1e14601603201e4a9ced90cb74d00433b01a44a00c8a200a1a20e86a281e82b566ee94aad0045ba7b87392740949ed9ce0634a707b27283d729406d00564406a76900dc0d3cdb6200b40122ed01628c4083263588a304a689804b86d170b7192ba37439a68028596b304cf1978078c9e23b47e09d8dc0469069e7039861061ea08089487873b55514a680271da5a9e71158d20053e0a1cc0b975a83b709588a540118eb0304e4d00223d9cf38d4289c1bf14402c0e2a94500713172a3b6094a68020ffe822348010ba3008051007a14b5128b73a9b564a61d8020aded55ae4b38d30c9c68874c35c1e506e81280b050b060341f2c774b894d005bbb19cdab8ccbb946105ca3286d519016a01b2b14632dc16a82e071016013a0e6792d310a90c9a7247dce966db1175a00a6ad869056b7462b52a100f45a4f515891eb0566ec94c8300415bd44ab2248a516909d2c9bdb25340126ce6b113b200705889403480b4412a2036e7572ac94d004ad396de7d081a1685b727220881910328d00f7464036b0a352548341a4e55ee8d929a01e4a64563b2488b46589cbad1db25301291c666e90e6774833a820c8d03ac62c3cb1429db84ada529a00b4b3c409169c8a0266f4b36c9aad004b54284191cd6fc860e76401e0ba900b202ca84805e568edd929a008de72f5463d1cc09e99504d0620252fa0b387b260406d07503c0abdcb06a534017ced44803da22f1ad1000d687c2621226b1c9443560e27076b2b88ca72d005a57e72b2bd29595d04c82c024417a5380b5c0aac80b41ab796c401641802da41742016405b40900bcbdad1b2531aee00a4d4827cab4131558a88aab6420268d2d45a2dcee95529a0082ef4bb10704d08302592797308eea9847694a02cd02c6202d8ee9659051f4d00463ba141b4e867d4f428aa60bb353d044a9e809c8f3f9a45f60323cf909182c8d40add652e2c592d1dbcba53400c7ca505d4a1201e405950a842203f22e756ae94d0049939aaa
def v3_2 := D 0x372c6e9b78574da6fb66ce15b1e803474985a2de73b8ef239c77882e3b1d0713e62a88bc28b3b0a82c793d2daf2534036ca0bb100b202cb04805e49e8ed9298143e433301064e2b1a26163d108072e0f290a76c1a94d0044f7d4daf9ea6c60f535a6789aa43c03f19d01d6ce4799e701e6615ecd828694d02a05b425415158e4d064716201e262d84b2318296445c568e6ddd29a008a372d5823b5bc09d95a04e8ad3a72e6171872e08c3961441cb2210234290e3960b1b502843f2b66894d02a05b3b4f07dd16e02e93b59a00768ad4585ac16822d505a13ee74b36c1a94d016328b923409a45709462111b95a3b54a80259fa8da04f45baa723663301b00980d794a06b02403565080f82ca4058b4ba379640105680219daacfa79c01b86383d1b8cadbcee2340110e8899cd0e92e7504113039d29407494402e03201e5d94eadf879015a00b6a60099d4404c816ab2d42a2c7c55b9a86a530b4014e9d39cf043ae64754f3828e59804c06403b39d5cb70e202b4016d103101d652dcd829694d00415bd60e19eb0610f582867232851160899c01004e181a620c085101100d8c016d2a76ab294d0048bb10804b25202572acf388dd09c46404a0d192301af1b2463c7bc52dae75340118eed005c4cc3aa34d89103328c4048ab058c0d5288a90168d01f795a3b60d95a680290165d800a2cc0040b5001c528006290002146036292880b42444850500d94d3d9b04a530e974cd547b819ad682d4eb306641d3611c496043d0e965edd29a00a3e8b310d531884ec844194201e0b092806901704254406cdeac5590516d00433300e24822fba3117c9100740d40717b4a56e4a556020c5e81f08c4080a62336529036310a1a44c0664a501392200f91cad13320e4e86de550069a03d4b68f624681347cc128c422372b476a950046cf51300993587445ab82100ec11662217072eb6c94d004431bb130151224802a84e965ecd929a008d0f3b60171366ea8f7244c3ab22514f651077d2c406c0575900d2b508222e2c22046d2e6b56fc8327680290ae09101c125564048f312a759740139641802daa06e0d1e42268313bb200f4bc1a9685c80d272e74b6c828f680221964319401f78a0082250f5cb207acc900c6246034c3231858d29dbb2512b40116ed36013b9f4099cce046a6a823212419424317530476c1a94c38b0229d2763b98ca05cc9d02c64e41692700b09379e609b3b101e2cd20058d4465a10406e165e8edf1015a01166ade03656ecfb1b740d8db92ec2dc236016e4944158e52151212f4b36e6c94d006b329530fba29719d11592e8a598745323d9a101ccd4c06e4a5d2724560b929631c94acf62a54bb01948c487a854973b823ba534014d2641b52080b649805a639a54325c5a10b5c6004cc1eac890806c9e54ee9d29a00466527f011958c18802d86583c0b9adb253401c1c8b751a24e923504a7272af566c94d0049839aaa
def v3_3 := D 0xd3a0d8ea076c0169048c406d460a51a2806d52a6dcdd29a008637322077323e0b991e958e414ed31b99699000b08fe46203eb9801288695324101b517a39b7cd1a680298d5d1291aada2926b4772ec94c2d0044b903f19d01004e9434664a1613209029c9e214c48b22706091301110d19108889cbad9aa6ed29a0540b6b2825455d41a285d3a88220546ba23401311880d906146ad94120d0697957ab364a68581814af306d40e548ad2cd934222cba9cbdd3200b401058e69f859c01d4e03950e807cbc155b1a6e5529a00b7d42457e9e42b05ad8a54b0b957ba364a6817b83c9690704c48302523f4d3820a48404ca063b2209878d2dbcb200d40106acc76a8978234bf41393cc088e902ce3478271a24130d1c79468d04a3461e41a2d920d145881f6144064142a25301a13439a5b6094a680285d2e911100d17508a20880dd1bcadb253401280e61061039d14adb34a534010ce83e0e887382a28109a04061c404c4b63910a5878d4b9daba530e8116cd29105aef626c61ca5634b80b404d3313b432447a09d5caba1cfeb4014a208fb1062bd8c293eb60e575b0057ad7d29d64a56e31eaaf1b0a9fa983bdd4c001ea5f40750528b880babc4bc03da5e0b6d2e507697181b4880fe94180f48523f640b83b24a43d11ea0e8aa607a15701d0cdc6e066caf033b5f619d35b0ce55d867006c33b0f419d0da0ce41d0670a683376b219b03909b0680e416c01f46d256c94c046ab4b906d487025871816397c0b4c255a665e83332c4f709560b84a505800fce90b1c14817a2e69901b313d4564d492808e610dd6ae129a0038652c2ca6058b9a58b73709586d34010ce83b06b01d06e20b81710701b483305a41882c20e5bb0052ed40276c60130b102aa9b0e2c513984e4d6e99845289408866aaa4209513e0447611e51af8128d785881961440344382b510f492a3b6c09a6802ddd8f13b547405a8070342df5d918b12d846796a22fcb40de659011cd0d07358f4e66a46203868c46b4e772d88d0017329abd8368069a44c55a968453052e2eb746c94ab00417f949af9ea4c60f526a67893243c02499da4908cd1f006692833a496d9ca4a3ce054b2db9a850d299f600b684602358b8f38c54e9c628144024052a980147a1cdaa84a53401087f53202423b81114ca6900f0144024052c04a2d59ecd5298760085d7b4d61dcd6d82e655e5639aabd94d15cc82e876822b555138d4044dbb2d4db626ab4014f7726a3b99a100a95e0e9122cc0727290e74b7094d002070b3c89704e44b0222280f3812609808b7c402dac2ad582e50696cdc25015a008876a82102479be32824e4946456480258a2cc142e056add928486d00443a214a1028b9756b364a6824b8a816d4b413303b0cb071a73b56094a556822dd33c01f19d4cd0ce006866dc392db09099a78c060a2604e422825c8940bb842054342a94505a131a3b4c094056802dab180d881c06458717616381b0b8e4d001e764036707012cd82e804e99166cde129a00832f2a45634b462ae1933a79b564a680223dcc49819a9447d84a03ea21f9a4068cd98852c8806e2934a52971061a13127e169ced84426a008c64a0023480411176809c74c04c3a5b651d28128e922880782c580585abc9da84a5340105bf5049a845901299a042f4b2e76c1b4d0044439aaa
def v3_4 := D 0xdde399eee1cad66365350c519d0e798531346035232a5848f95a73b611510da6802d2c890b0e078b48260ac0e80facb9daa540119ad6b1c8d9d1b76c90582b276c519a368d805d20b09175182b8290bcbad9d325313ce00a44288e112821f2ec76ac94cfa3b008bb48d0ab12c8d40a2d11745a397b74a6802577c95806c8ac3b62e297b07120d804b5220916386a9450421ba795b364a6802325cd3a4988032c2864852152313a3795b64a8022698ccdc404f7ac826b4f812bf26b0c84de052e405cb9329dbf25340095cb42d0254169d1a0d42908aa1464351a602a8d280d5c13149316404912f4f2a880344b02a05b5429c132cec5110a604c73a8621824510c10a8406b165982c5adcb9aa53407a910e8d9068c6702a2ed0db080e4d022106202e914940ba8c54a5805e569ced929a00873735453eb0c74ac75117b238ee9115d766a9fb76350e1a90eb0948622444b982c142c15017a44a3ccb4224dcea56db38e5a00a4e6af6673032b3800d19a90da8c782d452015a2660d49cb8ec0e51340725d9015a41a71e46a101a5e5ce96db11a00a966aeb86720641840e7056b2cd294c820453aba1b3b5ced1da2b14ed7300761719225cad9cae440e42e4a5022590ee5d9352990600b68c4094ca764821732100e8a0ce22a431e276f4ac94d00423b0aded3804640eb421e01568109c1bcadb706d340114e80346a000ca100a94404058d4a254100500fad39daa02b183c096aa26e0966ad2ce349b2707ec12809048c7804930f1279ba6c4a6802139ec376ed61b0d6b0d41b586805ac3306d2191b670c51b00f92d274c1c90b125dcdad6590956bad00532292d0406911216a02806d4e8a5edd2989bf00525b85b22742d880d46c10aa7301344c082036a0920101403674f72ac94cfb008b35810132c1679caeb64e4b10252ba51382c129406b845423910f51a7b96c4a6800c7968ec068d8717620442b10200d8b2e02c5a79f42d392a169a2d0b4c2285a58560d291b017894a4428b6597b364a6801c394c4c2c20ac4902c09097a5973b64a6851d81a1e76a82786b812c776091bb424e3b8025017933c69226630f465d8e6ad7129a00826fa13c33309a09980d94a023024012a1b0ea91ac1ec50b56ef884ad00443b55978333caa79802c32d3903234794d29db2486a340110ebcf08ede18276f3823a79a09d1710464600222f30b18778a04089005441200f1287b360d4a61d0229da6c0e66067b50e1cb541f525076c6930d4a6802d7680d901d2291882d68454c34484dd3cad9b25341c6c0a490027246c11925708812a8420267401c9d4803e6cd69529a0085af03b554906d6a083656c8fb1b62158d8906c6d801636211b00f8b927223848fa3b57964a6801dd94a8f48cd1382660b31b30f6a24946f082e7a641802da49c6e84081749247d803e12b3a4c09161c994bc2d1dc04ad2a008c65e70247c5832078a0906da542026a1295822e4e15ed929a008a627505d0a1201e405d40a842203f46f2b6c94d00497b9aaa
def v3_5 := D 0xd420d8f0546c016909b58ba8c09ad585e94dee5929a00a5e53218b3803a9c072a1d00f7392ab611d14a6802dad0022204590805700aba00b15493b64a6802543a2e9ab49c68b123c694e5edc50694d0053475b271c58c8fa1439b69df14a6802d2cc09909904e5d43a30e8e5080960c82c170876b2d88d02a0443b2362ac4b225828b445e8de6d5929a008d2f3e99730f4a6980229483d23a30137314bc616a774ea94c4c78021fbe8f886a00e0d20d2103c10b20b42431205027a79b554a6815ed5aad040b568156834023200f5482892a25034268b34e76e1a94d01bb3094f395ac09c9c414441c852a40a2e89526cdc2529a006ce5b55086a69e4252034160079e62e4d4266488e2f2a774b8872d005269e3753260ba9ee3accf403666262aa2ec0d513b0ac49883624422a91680d489b4a843083427b45b0386f501ff2680630b303881583fc1a41fd0c20fe0290531100ea48a2804c68de6d5d29a0548b669060e77740b380548c487947853b723b86a534016aae0ced9882660b01900f2cb476c9294d00433b4b93ce2339a400b2c18e48c261f0c74b6d8229500463ba4c1703780b002ce3613964c8964438bd1bacdb78a53401482f06d41703660b41b1050ed804cd65262c59dd2cb32512b08110cd5560013a404e8d6bf14e49e9233af91300bb88a72e8828f6439b56e4a68295816c7404d6399e72b59d3929e288c723ce16aa27053a1100f6a5c758b448e262af66a1294d001732dabb86760b8123aec79c56f24e0256c28b982e2964dd825694d00443a8941330f208d02c06403d1bdcab232d3401049f6b15af658a81b2c530d8e2846c025a5624620bc68558a61a2427de56e8d929a15b6052d9c1206c4e8c36244201e8b2d4562d4d8ae5dd2990600a07699e1ba4ca05d2639b47338bb099a59805b68a1a56bd00b5b50523128cde6ad445355a00a7498363a451b005a45c92882fa8447294a8909f795ab364a6802a19489006cc47836423a1b111b0d804c1251882d2240485860809fab597364a61d80af94d503e048f372a100a1b18e84b461f04f56ac94d0041fb2dd4f8b998b804a5f94660964a307e24983f050c1f78250351a201182ca4058ba18b976401a680229da8f82644e0129a3c19451d04a02443441e4a8ed710e5a009174c0007a5fde352fc01a97d70e4be42621626b8e8868e1eb4772b88ca0ad005b4a457002da11564201795a73b64a680559aab00ec14686600b49ad07336a1316203a6374b2e76c22950045d79a168e66067c14398172c5476c4a30d4a6802d39e0b653204a8c802d264c1515980ac05da252c44589d3cadbe5340116caa72950e2e94d21edd3361a34a6802daaa
def v3_6 := D 0xb3a334d8aa1a6cb3ce41e035a405cb151db2486a53011ae8fa84200ea2295042d0a8e6d9447a294d005b18e348c32b24542852132308c84a462438932d9bb8884d320c016a0f7dd00832e89d5f6c4e80b62730dc9381ae43421910f4c04712c010f137a59b7231a534014d164356849c3220b69a4e84b13124d255ceadc47c69a00a5d10e60e845307400943a05420269349ea13123e58ae8d90169a0082b7b005144402c2100b58a4620342952225182407e55e8ed86172b4d0052fcc1acf32bd479866a3cbbb201384ac0930a45c0270e7374ae94d0043eb91967590c206c84c3d541741aa15c0d48c686c07633501e928c4912961822712a6f6c94c3b051b354d68ab53ea0da82b569a1c0d1a2c4b40e80d9bcdad322c2c2f6d005273c13d0e609525998c20b926105812882ac9006cc64598b5a129b77401a68022dda9d83694c81340e60b1d4b06c8bb02d22101500d88c8871a379b57439a6822d93c001e9df18d4ef006a0e7934e9c90d1ef4772b89520ad005b5774fa1bb8950d6c2686ed914376a6917420c8d6a4681d02320231a40ec5a101f2b56e6c94d00ab72941d19f2610cf58d3e78c6583c63099db1790ed8b2666c5643347e19931030c98a3672c4cf3819290f0af66a143514a6802d88603591ed9a88a209443076402705bad261297164dce696d928487004632b90a5c20b8735b5e4a680229d02e39e0166cec08027605403b02819d01330e8352311c4c3043ca5d6cd9452990600b6aad300d9e8076ca9423600f42c1630b6a0560ad1c136f2b746c94c52780298b00f5c57078e2b03d50f43628720f1438058a1903b51541e98873b0c4007861f82c31501e88980f044507608e03903f38e692838111e9c99133509101d015acc39db623ac012d5941704a00a402ce2ea0964c88ea888bcb9dd2b253401aaca51104785bd539442790010048006ba30870510434a8407d045226a220a109c21dcab2533ec010ced2ea04e4b08223868b38c2a09c61314402c0e2a95900713172a3b6094a680210deaf804200c543a1c4adb2534010cc6ed318191032d09332c2d4484e317a5973b64a8020bb848e6e28662077a90e5ca841ea70e56cd3c94c0453a1e01630ee5d907676a83aba541d05b10c62d486214a416b7321ccb700d20b805905205e23584088fa3795b6c43d61d029aacd009a01d105a8205d28bd9b04a53400c4cb4690346c111b07bf2d03c42461108310171494ec54a51eb34e76c94d0042f398a5825742c132a1509883c46443a09945acc621cb20c0168a3a052161d4424c5ced54252987608b7683682a36fd7b0b78ec45b55420268d5900ba834584405d9e4e96dc3529a003ef2a9d9a954eec882c2895916c2a291690bcad59bb25340271ca693079801e0e5301c5cd141db04ac352a008c775a356ba101b59549b620405b25e06c67fc163e78158e9f06c5203d520405a90a8950f3b49840d0b43ce8861e72410f385e679bad337ac199e6c04cf359a460b83232862a87ac8d449d9a420aa320673c163326660994a3dd1ba5340071ca5582c20595202d0a02f34a6f6dc1a3a68029aaa
def v3_7 := D 0x1c5d373df40b99f8066b8b1ee1c54170e287b471305a38902c1c441507a80a40aa2808942d56a2a40221509f927a5b6e4a680cd9034294c8c648645a27006510809a1c07a89d00f982b3a64a616800d396d6019b04460c402d2717017519b15d00bacbd1db2534011abe5450242a18d3850668c01f3420267419c9d4863dd6ce9529a00a042afb595413c13409182d145a8285a953daf253400a8cb5ae0564bd25b205a4163081ad080b470601b795ba364329b40a814d40269172e0c8b9646401da562e8468d4ab05b4086e965ced929a00d4652ac2e72a40b8f9528b364a6287c03c969130ec88906e24081711640b09113ec0631b301b81cce621931e74eb36c9a9500463355a5833ad4039c69f54e34f2261a75b28d3929469b3c634d12302211c10f4ca736d894d00513a9409a003a45d05aea115c41597a37b9564a6802503cc6b1c248d98b8113934ba5646539a68045d41efba20e59d00832e88358744223d9a101ccd0786e483a2720200b920d31c86343223195a019ad9272a5848fa7953b6514a68029abe848c01ac62c3d4c29dbba52aeda008675a0ae7ad0033a05894a4428b7693b56594a61d022dda5f1e600789c8e609921e942f36c9b89500463ba281b43540963b8048fb683601348ac898c8ea115690dbca9d5b25340104de424836a1225b408e6d984646c025ab9012b264068b248049fb973a540113bb4014d55b5173cda6a1e6d23ce01ec32c1e49e16cdd44369a00867588a20759822a08272f0b2e76c8ca13802337cc100a3482801619356b3754a6273a0c016a4f68f80832609525284a908825344202e83a81e5ee8d51969a0084ffb483df74020cba6391ecf1c0e678dc372c6d13956f05cb1a98e423a191090ad00ab2c93cc2c247bcad1db0f0d29a00a4a88276e0a529702690b802464268b28f2551593782b5a64a256800d396d37d33a5be49d15704aa6f3673374b385b689c15594a03c4e2a64e8510e2f47729894d05eb02d7940d4e9416c1e5ab50f12528f090cc05d1311017514b14500bd1bacdb2534010f9e45487660c81a31320c88a83ec0481340179834e6480d1e52b4e76e928d004433559c81b4c0eb4ce7136642802d0059f480a20a406c272025813250099d2dcbb253400f2ca411326206ca9cf30a871f476af2c80b4d01ea5b2812b4422d468ed70250e5a00b4db02726301312e008c8bf0444da9660665d303687941b374a0d91e406c5d2036078c1af7460d716206b49101db80a88bc01e74f6abc94c3a050bb573833b02089c55e14c2e6b2417345100b18e18775943b60a5a534010a7f55d1a64ada52a5801912be34895b1234162844e898311eb56d2ec87b4d02cf02d81113400798c169324482b26b4736ec94d004a379a5a091144046b5e28200f6a16096683c4a9d6d844269a008b754296a0516a2e76a1294d004607daaa
def v3_8 := D 0x6e40ce74fca71bb0130d386906eb4c43750a201a01c00f4872f6c2294d004193d52295997508a91718bc1bcadb25401286c666020c9f58e00fac6967163003809700aba00b978153b79d0d4a6802d4cc51f2652cc0080a6087012843e6902641c212a22101f4396a271653674a9534d00503b58f553924ee8c6451443223a10134100f511201f08736ac94d06db0219d710fd9b870acd6f8366e180b32aeed915786c435068092105088c4011b873b554a64efc014c8d0a1581a46a05422e01ba3795b64a680b1199eb009af4878e5da0273e40231f1e910f8e2087c6cc221f61960ea2f566c1294d002b32d19635a8ca06d45e03663251b0099340b4ac3b21a805893652e774c8020ad008b354069520032e8c02de8c39769307b8cdd2b2530f3e00887602245700d42b800e904023c6024c1bcdab253427ac08676a7009901d494024a84a8809c3cada86a5320c014e8b204f0808258718f3838a09c1c404a02e062934e42313653ba96c405680231daba00d9d770eadce02b57597a8ad23545d566a2ea0150a5415873e3485d37640552b39d48b4e3e8e1e6d5d29a00829f240813c1620962d80ced6b9e70b585385aa094069a058c405bcad5aa4a5340118ed29013394a79c46094e006ca5012f18f0eb536eb887ad00463b4d491003256e7810da042a5cdcab1b95bb4f06d3401680006a00d7331122c9a6484d4dee55006008246b556ab05ad8182e3aa9598d528c46a854202cf5a400b52c9395684101f7953ab60d4a6800ffcb146ad2b315068b125da94de6dc3529a00bbf301a64c00c4a5006211007540f22f746c8734d00427fd26c0d90c686c509c3600f1494620b48890b0c10136b2f66a94c3b02db29a04c091e073ce6b79a73439d19c0c79c5f744c034452a144147ca9dbaf25340063cb5a1276a8441b527e0da28849ad31aad63a016351133526305a81ec4c44fd5b107a7cc8e85645a49cd0d2016868e330347692085a320b45b151dcb202d3011acd311d900382a82201a40554441101b3a795b640e9b4010ccbb434e8d7ba3439453935a48cf5444c02ee221cba2083c9ead57929a0a7e05a14e33d0a419c8513ce0082a701259200b5b147173050f159ab76994a680221daac7ca90e6064a01a0c318fd608cbea8405c4c5231858b9d5ab25340107ec3bfad792b35fc0d9a187ac8f383642922aa0fc0d53838aa4e083529e0f5940a0ac9090d446282a26f1db00dc3543c866a06a3d40f1c9a078c5cc3c50d61e21630f0c1587841a83c10540be0b2040b44405848300dd4c39d93a530e8114cc02c12c016e9182d1458d5050f8573b5114a68021d7e81a5483e0ba300b7614bcc16e7374ac94c3cf80219de8f77ce0633a70485f3023ce9811974a00712304549100f894b505c62214bb39daaf2530e8118ed45cce202c5930e0901754a73b654ba53401496a8948068b5445284806e965ced929a0088e73151068c0e3481c8b4203e25cead5fa9a0034e53c50320e1ca906a654438eaa101265e96cd8369a0086627498d04058923501202f4b2f66c94d0049779aaa
def v3_9 := D 0x6fc48ed8982767c811ae0679c69374e37f80707a8610dfca08088868838c1bdab04a5340138eb7e056a41bb200b05d44403480b2a882203742f36ac94d004673980b367765523b02009dd9b00ec070a321621820e42af66c1294c83005aa011a8038352720c4104c82d129c243050502773ab156430db4012d2cec85258719424e90d66db3c529a00b5d74674eb5a3a5d609d3ac00e8b48a7224491975679c16444c044a429046142134359b5177a5340a816c8d8ab12c8960a2d11773a95b6105d34010ccc1806b2f602c3e859a80450cc2c77643d00b101b3c24eccc291f0e7374ae94d00433790452940f734807b3a300f4516a2a16b5276ec944ad00503b54bcc1b5039522b4b364d088b2ea72f74c8b1b68020b1cc236dc61104e2b58171842e3884de0b3842e405932a5973b732fa534014ca92e72a10b8f958723b7690d4a6802d3d539e1f600f0fa80683887333e939c9f340e4f916707c443828659809c870090b793ba54dc4056802da4b27145e194a2f00a200e918b522e05cee95d2955a008a75999670cc4b280ec68c07624402563161dcea56da643529a00b696e79c45534801503101cd2296d8296229500463a8481a3ed0ad002d68b4a4ab416249cad1bdb06a534009ce4139b5607392d493b499216294a736e736cac8bad004b553b404ecf78a320b6214e592051e42eb566e1294c527802d41e3b981015ce378ed71b896b8dadb8c6c99c56b3ae31adc718c0acc1c5462054d9835318c901a4e2965cedc95e94d00535729ceeb782760a25280780d80724359b6f14a641802d44a911a2e3ca0152b289162e16e9cd928c26cfb005b589d128c4ce8c62584401e882a6a8a07b9a4dd2ba5342b5c08675b88262d865106e128403ce80393a90079dcad2a53401190e0764685589646a051688bb9d2cdb20a5da008666e90277d70133a9008cd46982025634e2c5b9cc2db06a53401053f444cf682213730f80b98875ec83582a2218fb00cf2d402e3e602dcb1027181489016cea7572fc280ad00535428c169c182c402e6f38b9664b932238bd1bcdab20c5da008865cd82565cc12a2e6e8d0d314c45b123234d13816d29407c22520445c25caae75340a816d4643b2a300d551704aa8b4760034d980ba4d274d50989272b476ec22950041f3913209e96a3ce0b4a2705a0f102ce88805c1cc38d20ba6134b95350d4a6815021da52291a5a31130c9ca39d2dba534011afe51494889174a72f6c9cb4a68029914a0c559112213052e8752b6c6834a802319e8b39d7448ce34f9271a79d3009b0da412c3c696dd44529a008b755394a87174a906f6e221a34a6802daaa
def v3_10 := D 0x59f1ba21105d37326e7b8a673dbe0b9edb51cf6a26d7b3c16bdef3b96f609cb7a82e5b2007297115093f56873fa53349d5999773489f45646ff02e1968070de00346f469233e28905f4834f5082d1f452c76c1a94c046b2059b3b02009dc8074ca302270124188e911821ea436e6c4b34a641802d8082251619920b0c2880399547b364a556802125e82204607b422008510807540f2b4f66c94d02a0427fdac92f9e01c6c53912c147ad1a4db1b7fc529a00b5cd826652c12a2bb09885904642f227017089481116916b2b887ad02a05b4f32ce56e02725581299e499c4eb64e27502501a07150b05b0071761a3b96c4a6802b1dd260d976816c4fda3600f483125105f5082c52951213ef2b746c94d0b470291cd3da0e502d07200e838c0341c43d98e11dcc702ee41f01721641ad0ad05686fcf623790b11ba8188da9da46982d2345b610f60b08996d642f02b2370bb01b62580ca0aa060cb5025d6900b92c80b19a20564b106f3048e4e0121ef2774a9a80ad005354114123cfe19d67e3ce33d1e601331930f4832f6c9b88d00443a74c1b53a66da03409ac6a1ac6350169068730c1405a20a1ac104e3984b334c4113662090130965a888220c40ecd2526a45aa09cbdd425340106fe6a9859a54b1cec9902474ea5290998c9876493ba6c114396802d10e09d1d004c8e6865427432209ac0a5480b753ab960d405a68029da61c5d88116ac4083362cb80b1b4015858f46c0367171c9911c3e5d6acd929a00a0e52bec1b15da7d08130664790322c38bb06020d830d66a1861f40c2c9a002a6cc0f40640718a20331280ec52c01ecb2f746e94d0057b3109048e3c82432b490807254271610ac127752ae6c94d0041cf29d5fa0b899b0547b0a241d81118ebe8c475e542036b05d00b5210a9016d101f65973ab70d4a68085901c096019da602538d8c809c351dcb6202b0b4016d5547c12a27209493914474f2e71a79330d56b946a504a355a621a945101310e6415a8899d4adae04d340122ec4f7dd22402e9139f6c89a0b644c36ae223b4512e7712340b891975444e542ad28d332a89459b6379b56e45d68029ab1024357c1388c409446254600b0210174196a4316e974aa94d00415b0c5ea205cf40e252910a2d9e4ed596529a008676b0c1340068a16025a8a8148222e8b472f6e94d004acb918408d35e7ce59146700401386a318c34a74603443441d9ce56db929a00a3764d7732498b2e989d2cb9db2528fe00824726d55910382e8449016d021359a73b60da68021990dc99e86974e836bc5217c5110b889c05884203630291602e52e94d8250f415a00b6a84b9421717285476c6d70d4a6802d03f19d3d95c68bdba34f4453918648cbd21444ca22601e21a20ee556abc94d049302da83cf413865a005ac5a049522360135973ba64a6802539c93f0ce80e1928d206479351dcb24e202b4016d5bd9dc6dd3ae21b1d51076ac4402c68b44110173a7195b7553a534014aa205b0e483667281b25427d8aa00ac54f8362a780b153a950a9c16854da3602b3814ecc8051eb36f46c94d0037f298a9034326cfb09347d447466821c1a4107cd080dc5169399a5cc3416243a63f0b34e76e221b50046327f811ae5c09cf2d0cc7960263cac1190a228406d8052d005b9c4adb25340105bcb74ba44440345d42288220372e74b6c94d0098b29aaa
def v3_11 := D 0x3c58dd38782e9c39f6ce1a0b670c768b85cee3be41713eeea888ca885a4532a8a059737965b6e4099b4014c6f05c47faaa32249a00788ec1491465909392a735b7259d34010ccd6b8f28b5248c029794ab564a545b4010ce98404d0069250451d2008ce8c28424402e4f2a3643c78d25cbb7200d301055f69060e77944733054d8a24b0b95a73b636386a534016880285212005824e56e8d529891702a05b4ff9a69ca0334e4dd99076958ba11ab86a5582da043f4b2e76d4d006a32d99f5c2d47ad7c43d642200f4aad205b42aad4c02ef46b36c94d00454f921a09e90c04c48582523fc1381c2a8405c9e63b21e9878d2dcbb200d4010c98ed569648ed7f027679c11ad2a79c69374e02ea3685458c1bdab04a5340114ec2c1dcc8b82e6036563856bd942a76aa14ba541b48c0e8c90f2f508903e84f4b36f88373680299178d245915e8c4a42f46f2b6c94d004a77902009da0b00ed05046682403309a1047a89010f15b735094a67d802da5260b554784c437c32296c16809a666752d0c9326346f6b2e87322d0052b3a3b459f1ba3305dcd94cce6c59573624a399134d8c6f82c6cc037265293931605c98900e4b38fb159e7b89139a446fab22cd006867e3300a901819fb4902a54482b834a4168b962a3b6494a602359888026b3001298c64984252c225f9210170314846170d6b4e6e94d00424731dd1e0d91f616c7afa3600f482482036a105211120372eb746c94d053f029084e940417480203a100f219494317256eca802d00445781daab65ae79b2803c59619903dec53972c147bcd1adb2cf2530116e9644858703c5a41305607407e15ced52141e0466b5abf036a073a2e2966d0591262b56e6c8aad004163949e19e24904f0bc027676813a2f069c80f0c811d18308ed0104740040988853a248947ab5b9aa533ec0150ed01a44a00cb24006451007a20c14d45099093417ba564a55680219d6fa0d9b7c7ec9bd8564b581b26f40591c416c4a7a3601f049489202428426eb73486e94d0647029a6dbee93692745be4ba4d961d26c0f6656d5a00db2c470e5858226550f276e6934a68029ed2d5af6206d65b2d3475819af00158e9306c507bd520419a9efe950f7e4987bea4437849a1ef8430f7b2087bd2d3367419985d348822064660c550f251a8cc09505e04680b671b1d9b12c3e55ee8d929a00566520c412314819c89e04c44702702341200b5c987262c92c2728e774c2280ad00443b5413c1acc7a0d402e6f18518d325c89068b0d8d1bcadbe34010c90c81f8ce9ef1c7404013a7d001d00d7468630a7232491903679c1a344c04c8529108147a1cdaaf25340a816d4e1bb1a6b0d896c0582524c900325480ba4e2e0ad622684c88e427e568ed7024e5a00a4c42ed65bc16b21a1b18bd058cd4ced46a016a13e1b10660588d386e236817134c7b49a505a4d1cb30691d901dcc1f2a2d54332407b2687d4de6e9b005a008666aa7b67d55433db96f9e5ca60f2e5a67772a43bb9219d3c30cc920b663721031b9279c3c33cc064bb291db050da529a00b56003c60749ad26101ed19ab13181403f4b2e76c950046335a43036206c1999460a403c16122480b82109c4d1bd93a530108eca66c00a71d41930e9ec9003830580605d1cbda88a534010f8f42b14116172a5476c44f0d4a6802daaa
def v3_12 := D 0x2e88e66cd67390548c487a98573b7095a8a534016a928a2076d424454104e6e28dd66dd29a008cdf35950cf905367b65073bb2641dd940ceac99875634b380f32f0a76c30f0d4a6802d45c0918cf048815b129044b489337b9554a681502093ed02994800ec2296042d0a8e6d837c529a00b5c92e74e44e3a5be69d39000e9bbae64d542325baa992c400c8ad8a725645312b689c15944c064a428b1c356230a10fcad9a64a5340a816d3ba7719d6eb8b8546201da2bb16303d4a51a88bac168d0275a973b652ba534014f9507b35803d5aa11a807a41241040fa8c04a4048501f73ab1564199b40128d106d45a83682cc1b11a0ad804a60238920087a9dd3cb202d34056cd567c0cef3d9e700b0cb4e40c8d1f4af276c9388d00443a69013b816794c0a98a54a4a530240298107908803484389232a4d1280fe69006f24605e0368405cbad9d32512b403c96c6a016c2e80b4d4794401f31a1cc91683c565ece9f0e5a008664e9ce6874973a39009106744c09a225018e5100da40ad080b957a3b6ce4056802daab08945d86482ec0a200e861ede529592955a00853fabe9f3d5f221eaf83ce17b9e50bd81285ea7902f46481799630bc9d185e25881f514405c5d88b93ab55594a680210bed130d20428c8c028e85148da0f873a5b611e4a80231da60090d3f046416b459cab4163e628ded844369a008a7404a3600211a800e894006842025288093006921e25410048d69ced444e80ad0053556b22ce7558263ac4b38d3f29c69e04c295b241ac05100f0526780d098f7923ba6114a68020ffec3d04d61e02510ecda0079522e801acaa115c4201b958b3764a7580219980b367604013babed99d5e24ce303a7544dd328c089c51344c044822a148087a91bdaa9ed2990600b50b86745b851a19429c8bc1464de267068d13042518c078805088900f3429b56e4a6815045dac22bf661007b307a3500ed59c82081eb458748090a03ee7562ac8513680256ac19db5504edaa0256d4c11a6a6e8cb525460352311d4c3443d65ced529a0716051bb2362ac4b225828b445e8de56d929899604333b581723626ad75584a5decb22125c4d292d50425304c49f5793ba6114129b40148685ecc339b5619836a0ca0b506405683183521881290c25b805c05c0300cb017c148178cca4498b5937ba6c401558029aacc478c6264463183e218945100960e607314a9b574a685838110e99a06c8f6c360f4cf10078a4a3105ac44a5860909ba597b364a61d8289994216a041730a76a1a94d0044dbdb000d901acb480d6ac2b4608cbb1badcb25341c7c0a4981ce44be072262bb50c135a8971ac44b575a2586ad1356dc43382e24d67690ce6b4934058499b6b24c81592625b80c105c09804d04bc46825c0b012d2d609602b0579c4a89564d8193049a1f53a97b6c114018029aada134206ba46045aba8448242f2e774ac94d00aa329350a9ca9474a149b240a48510522a8405d125175148f847ba564a223b4010ced25892892a49049424201d012a8422d9256cddd2955a0839e33bc8192002b0cc71f16201f1362d350c3398acbcb9dd2b2534012c9e5498609a84d090266c352b6f8897f68029aaa
def v3_13 := D 0x70a06c5e98223c241b0e1009404d230490207ae51508b052910c04e74af36c94d0059b3218b3803a9c072a1d00f7392ab6515e8a534016d59936b43e0b5da805c6d3b6d2a4c16992ada887f7546d31ed0a48168b4a7b008205805f23a1d59986d09b0d2dcbba1ec8b4014a812ec14012200b48ace3ea11164e8d5e6db9298082af35935eaa762cd53af56a01e4ba252c85b4124e965ecd929a15f6052bc41b50392e86891acd90b68988a43e6af374c803500417f9a7e1670075380e543a01f2f0556c232a94d005a6ec91803c456649822ae3135a37b964a68025a9c9032ad481036a4041b42000d88fb66c02e4982ceb242480b0e5d6acde592a6a008c66a97294b85174e6b6bc94d0045badf41918404d441f24a01ef058d350b90160cba539acdbf25300d9ca64340b581d331825a1922409d3cdaaa1efeb40149301500b5241134405dceae55902f6d004b551413410a09d06804441e892d4122e055ecd83529a00b97597c6e8c5457459a9d98de068d66af64cbe771650f38b1505c588a0e23785514225d82102cc0660b2aa602c7c3952db4ca534036cc3841919784d002c5d60156457168014b8a9d14dbc25341073cb64d2034675015ab508d05472461f72320175bd2092a5ca10272b4e76dd4d00f2520c813d068f9e02e04ec1982660c012905a08c82424e011921022c59594c163da4d6ad8352895808876aad8a3d9ec42ec3619661afd5a009aa4472a2410f4973a5b7514a680dd90a879c81014e6389e631b893101ac90c792ce230a2711a8f308c889845e348055a731d62d0e989d1dcba88a534005ccb605e091d6d04a01583581e128e5edf1185a0088751f02788f5f33478099a3d4cad1e1a560443232eee9d23a3868bd3a3476453947690c9dc1464bba2708e82182f488c0fd07503add39aa533e86ee00b6b16bb200705504403480aa888220372e74b6c94d004ae3929a6cd14d054416932b4262c65ed68dc269a00a0669a63b9cca05ce644ac73497b29a2b9905d4ed0456a91954e350113eecb536ca4b4d568029eeed9d6ff2ce408327268412964c89c1bd94a035c22a11c887c29dcae25340150cb44c836a2602b212e0d909606c448cb601738082c58e2641141586d6a6dcd9015a0540866aaa80230063a30e8da2c1ee752b6d9c8d00443ac0c1b23400d89ed46c01e097b80b44414af1c80dbc9dd2b25340a807fe6a3879e52800f179006949c33aa4c61d5256ce692387348dc31a4509489b470588d1f4a772a938872d005a6257741a20ba1880da8c382d44b41a930d1d8185668006a320224a24492012a09045ce965ed83529a02b66ae306e4f0c172b8a1d88870686e21330170254e402151f046f52b70d294c04532af13a3576951aba068d5cc946ae0fa056e9502b656815a91402348942968442c126af3746c94c62f8029a50026a074716a0e16a2f566c1294d003032d34e0ba81e69039968407b4adbd1bd3401091c66504d0892025a04274b2e76c94d009a329aaa
def v3_14 := D 0x37b0677bc803bdf819d6931ce008327047d130df6d9432594a37d1e31be49186048840b846c208b9653b5494a680289d2a0ea8c7e24407e23100f582c805b12a40584406c865e8d6e3b469a00a6b16b9987e046acf1e60a41a30b3ae9859c50c03603201c4e2e5590e69a008a753c067261c1314a319c01004e13b46609d1d3001ae8c0788a544145c2c9dbb725340156ed09456440e0b2540b202c215405e568ded95e74d004332ba81b22c20d8ba446c01c891b80b08a618e405de4ee95929a054043734f88dd1c682e8e2d9a39ee5d84f62cc02db550d2b402d695148c49f9837ab634dcad34014c0c068dfa02d39d9e59f384d079b0e23cd0b101b38e4ecc8991e32e774ae94d0043ef901a0950f184c4144d01d10d403d68ee571015a0540b6a978836a0725d0d12359b216d1311487cdd66e9907a7500417f955ef1a1d404ee0d1442974121832b0c8d884452da2400dd6181ad08809c60562405ac3d9aa530ec03c96ca26220ada292289097a53b976409fb40129a65db0c902d84b41a91660d09e58ec0f2334003859004f084089689124885a824117a379b56094a682ad9a85d15482216a6efa5435b05a1bbeb4cd6c0666174d2208819194f15402156a2bca5415ad5a0af2b4c56b466253cd20085190219c4344b36305a13597ba364a68028594b290ce9940074c9c33902029c28504c1930250c94d2064898832314404c0367005ca9dd2a6a53401064f621a09acb10ce237aa711941300978c787519a7b6ca68021931dd1e0b8e8905a4cf3aa26791880982ea2181a9480b2a891a03eb2e756d2a94d005203412a01929882898e3a2583879c5acae21cb40a816d55a601b2d022d89ba46c01e9148c416d422a61a2426dda56e8dd29a0a560531381758bacd445c74822dbb2012cc510b3b6618a8a05a73746d72ac94c183021cfcd598129acca8cd6404e1200210134416a281624f74ac94d004321f3d44891ea233ca008225087d92001c48c21f1440368851535140a0a4c5ee9552836ed00433b587a1a9c3b09496205801e938b9259154264471b17395ab7c4369b4014a90490406b460a5222806d6a5ced929a0085d7329024c4d03ea10484d10d407dce966d929a0094873a85d38eecc983cc6483828a2012861d6a50ed82529a00853fa1f013d0f469587e2ce032a2600bcf180b82cac058b63795ba71143d056802daa2cc0a8e6a3ec3341f51876510c082c405e6938b98d2e65a13223961f1597a3b7c096802219432b5a9ea06d50b95686741b42141b48c805a5c2052270c1916440d812766a1f382d0b1e5a07cc0b03e58e612c9530f90d987c604c3e24e41483d20f85d907c04482510620b6802d4802d65ccae9d29a00be662bc09650a94c41663524c5b0c9459d4621cb0b401695204cc8002562c01232a279815054c0a7aa505391200f340aca3101f0a7572c1a80b4d0063b5708111b7328c5c194201e3401d111a9009d39dcab25340105dc3efa95412b53889402ada938b5aa47dba1d2b252ab40152ec4141918eeec802c1758900d202cab10900dacbd1db25340119fe5eb8353a819b0642cd403d24b48175192b5300bd29bcdb2534010f8e50592a103480b08550a0372b566ec1a3a6802199aaa
def v3_15 := D 0x1bfcb3902029c9eb04a592a2707e65280b91ca989271f4c772b894d005332d2545a80220540910a900f38d00e59322d200e2f2af566c94d0a2f029ad3aa63699519b5ea8403d1c5a8b85ad4d98bba5340106ad527a8b5692900f22345a94a1201f795a3b64a802237ad65d06d44e0255970169068f50e5b0687240361890198cb40c421004204e03981080f836a92b74a602292196b61592f636c8169058c206b4202d1c1806ee965cd928caf02a0535016dc96f02e4569d91076958ba11ab86a5582da043f4b2e76c1b4d005b33eec130f749947b966a3dc0251edd320f6c6907262c40718a20237ac525a0811825cab15295a22809d965cee9d29a008aa72471db32371d911a66c88c8b624611b00b82c62081a405a3448601b495ba364a0d9c0a814d56a34ccf518e57a1db29a7428ce873cc29d22304d15080f48ca96123c869ced84424369a00b6171e7204053901c09491744e08aca5016c31ceb13271f46f72b894d002d32daaca47b56132802089421a6482ab9e3094c91843428807d0a5a8945bcdd2aa506dda0082b7a100a8900b95ab7360da68150219dabf43b9ae905ccb3cac77e57b2bf13b4df705a68602c208dd51bec8d409d0500253911b51110407de54eadb1050ed0052d0e3984a26cc3431e21288310133a149d416b2f674c94d00503346934c0114a40081d1807bbe864971ed231335ba754a6263c0118ee8c07a80e8b814806d41641284806e569ced91a008556a08993109809484b44e0102210134680f516a01f2c5674c80b4d002232daa808027da6003edbe399ede90cee48665b74c32628d9cedc70e57f1e70264115222170a4e76cd2a294d005a82e850900f202ea05421201f917a5b64a680ed199ac196715ecf2837209457e3c82be32415f8b18af8e8c57b2c40dc8a2026321e50c596de7529a00842fa96533b46731da2b04ed2c007652cd230f6e9d0646488c8c2625cd1301358c48b172cb66ec2294cfb005b58f636cc780b663b0dc84802e40345a1adb0c8e3186a023434022cb24a20b48ad985848504051bd2cd9b04a534057ca5b9af64d502b25b26d92c102c8a98b6254d1b00d6958b1840f08342ac168e0c0474f2b66c94393815029a72cf6b3901b59c60da4e266c0244d5852c10025a2d09b753ab964267d34058cf6306d5e382d996e26af107d0f874a86f08b43e188a1f0b348bf106444e3781d897203de496e8dd29a004ae522c81b51620da0b006c4579b6013282d20334992202c4c04c7d6e8de5900416008c66a81d0258290132c0c4886072c2339921016b6145cc176b2e6a94d00420721d4f43b5a1c05ac708ec63181635581b529205a9fa86c42001627dc0b8a7f6da52d82d22896900e08c81069a206b23103e9a6406592564d4b433023235ab379640591680298b782d94f011805cc2914aa3241a112e34f2b6d87ad0043324c01b4378cd81bb6ca01db262d206ad6530589806cd5e6e19006a0082cf3571933cb9c11da4104eee34e75538f380b22e876ac14b4a6802b9d1c20a8ac82e81639340b183880a22c405c4b63910a5878ad49dbba5340116cd104128040ccc02d2774a5a132e249cad59bb2512ee008c64a2826bb25d080538d3876953ba64a680229d859f44b94217172ae5076e6030d4a6802daaa
def v3_16 := D 0x6dd04e7660263490119dd279c69834e3741e61b44130dce58c5287461e90a202a01c00eb2ce76dc94d0057baa4dc182ea131c848171795ab6c4a680ed9ac58677628f38b12c9c58804a024f02a7202de2966db129a0083afa98d33c02499d81004ed3100769842334c0019a4a0ce92f9874229208e252021f2eb66aa294cfb005b590db3ac7809912a3ce408327203412909289c04794a03d8229042b1113835b95c4a6800af96b769ed56e036a5581b470aad80489ac5856c101204b660b428dd4eae590169a02c6652250ad750885422cbd1bcadb72534058ce5a0ccf2e06560b5814a901670f2b6c8547a680229d19019e8c790f4634a7831473b17469985b4e03901a1d013a3b7950d401056802daa14a0a881a46830483100f12d9692214b2b26b5276ec94d0046f79802d5ac0006d5da8564ed01b241ef5501066a9ffbf44ff92a27fa9313fc48894a0344fee4a27f52313f99089fc0734fdc29a4ba0cd3f63268518d421c85a120eb4c8d886648645503355a814e9500824680d595b1e6152c3de56acd929a05ee05354005d29f82d74667512e20a8d3e26602ea401c822165422036e74b36c1a94c82053270d73a0f929d15e04a8e12444705b392950989c09ca42f82422b51380f529403148805e63524c59ad3dcb6200b40a816d2951ccee90675744f380758c587785a23b724db4a534016ad48ce9699c748ac13a5a401d07b746968bc721f053915848cad03ce0a622601a4d2006458c0cac62c39bcdaacca5340a816c038d288be69002bcc55e985d4dab3b08a1ed40118e98c0547ab9751d59120eaa88c5345443aa2311d4d5080fade0b201ad0a97202c2203ee752b6dc1b4d010b2aae2f201a545911e1201ba37b9564a6804d794d55a9c7736040b99eb958f534ed3a94169a3a0b0a1346203c5980129c6a2324101b579a3b6c41cbb4014a912ac8ba84528b485e5ce96d929a00941735590cf2aa827944413ba2269cd5804802c4521d125483d58ded52990600a8749b83688481b1378cd803c98b48164a60b1300bacdb9c3200d40109ce6b02c6d981016c04a0ad3a86686b68b237da1a87470d007d9251056584850404bd3acd9b04a534063ca544ae469281231d409103f0c84092430089d1819030803c54204443441cd22e55929a05409c769861b92d905c8a9c3220e4a4cc2035524a84d302407dcea56d82503a6d0052394174edc6d1f5344a01dab49f00695a8b45890e610233795ba61140e5b40148503ce0241a70038d200750c98a170d4b6ec22944b00443b5427c135bf009882c46443b9dd2cb65340107ec675e002745c011a77e09c8bf04640d9e7066113077d2943bd3481de1630eecb081510d290443d0aa6d5b929a054217601409600a748c169359ea13163e964ded929a00875f3020169f810cc7bf16201f3362d2659cc564de4e96d929a008677249813424a79c11684e0919e6047613023109400d8460648a20226894e8c4462214bb1bdaa84a530ec118ed560d90803150e4ace76c94d0041770d7e96a8948068b5445284806e965ceda9a0088e6b4903dc09202e048c150078ce8e49126d07138973ab5709a6800d39498b046a960233c64f388dc09c71a3c63881231a951080f10e1a5443e55ced78369a00a2756824e588091ee52b476e44f4a68029aaa
def v3_17 := D 0xd26c9c70204c3488251c05310e0028805a007a5179b6c4a68020c9eaa4295082ca94e6d944fa294d005b59616ce8f3b654791b007a260312ea09610c11762b5983784a6541c0149a604f53faa629f95294faa8404ae9238ba8c87d1dcaaa5340106ac8cfb412816003b4f3172cb1332447173a59b5cf1a680292d00d996306c9d52760ea41b0098954902d8a51426017975b3a64a6802243cc02051101108402d445825410f172ab509954a6802df3e199f9e30cc16b9295322ce96de5907e74d01ea5a3d5f3d03f19d01004e87a00743ccf381e401c06c40539180147a4ad9aaca5340a816d53591ad579036a0a9a20510b44b450088a136b476f2c86ff09fb4014c2086a60fc25253c16007a4e2e49645509911c6c8565ceae3113e6d005320505680e0b2540b202c215805e0dee965d2990408a64709e707c0f183df08c0390050459240262caf66c1294c3b05bbb555c131ab0c9802b8055d005a14d59b21cd34010eff566276634d9a3598bd90d37545991760cc4ba8298ad007534603a92205311881558cb98163dcea56da64369a00a67060d54b606a4151859d225418161cba3d1adcba5401081cc64d082c0073cc5c9444cc911c5cea56d711666d00520981b304a0d902436c4119b601268a8a20b45a622a82a2427d0eea55928960031e535530f05d35e02d5aed9a004e6906ba76402d18bd16b66994182f5059f379a5b6114a8023198d40bac6966a22e3a411a1d90096628859db30c54502d39ba36b9564a60c1810ccd5c57b3ae0159d6f06ceb70167431db2adb0d8d0e46c03d30289224805044e16e5cd92994ff00528b4fb445815a22b06d11501688a4fac450f5622706b113295852cdb344a9d195e76c8af436252d1b044a7d00ead2516245c52dcb9ba5184da00a6b123e7b88cf395d609c9671444260429d8240a3ca516acdc2529a006d65aaa0e2b29a09d3640461b50a20d811080b9d127275148f3b75954a68150281d8018a2200a10805a4523101a16a11128c1203eb2f476c129aad0052aaca5458b93a58b77095a5340114e8852ed0420f66178d5a1073d887696a43aca521a65910f60b008cc64898b3795ba64d43968029aa14609966d28885102639b0f10c1c28861c0c2306aa101f1614cb1983dae54d529a0054e443a64013d55419997604c82244542d01117db19829038c1f63260fac0300dc9143ea0c21f4aa103311910f3634e6c80b4d0045bb51504ca461e71180d38a2879851334c0069a411799100f28ea2516b4966ec2294ab00418bd2cc09a89604a4b29e605905302c67881621440b08610582108116b0ab660b3419b56094a6815221da52291a5a31130c9a4bad1dba53011afd4e6026a73153255ead0aaf0665528360ab818842008407d2051e12a1026c75724c94c04334b347836a21e9a500b75a4f4334b8b121da2636b3566ec2350041ab319594c8c01da252c4458cb9adb21c2e9a008b7559ac20595262d0a02eb0946f6e221a3a68029aaa
def v3_18 := D 0xb35333d94b9d20c3ce01d63542c5c3952db4cf2534036ec7f86a63f42523ec160079c5c7264470f873a95b7115a1cb4014d544ab4a380da5517aca8e2b656445b0b34bd42904aa2cbb3516658a80a24d05980581281b30145d90b30aa82909a22cb8b10434596a2b168b536e6e94d00424b94cc19da6104ecef82745fcd394ca08c0590a23a44a887b4ad9aa5340a8150ed6488cf04912220b1b14e44b051e54a936dde294d005a57c1b52bead8b9a4ec1cc8b601298366058960b49c02eb374e6c94d00464f9a789b4006880ec95041196272b476ec94c04a5f199d3e2d9eaa76ca95a3600f44c0620b6a09608c121368ac76f2e94cb43802935644880d1a2d2094480db9d4adb2074da0096a8fcdce3cc971f4e2d2b6fc388d00443acccb380358c587a92853b724d86a534016d4e41a9a5c094d4a3ec2a4b3401345a4e9a82c4872730b476ee22950041d7926a0da0b8058ce903642703220751309c105444382a070c6883acec409d5703cc08545902f0e774b2e80b4d005335764f984a06cc02ce89393a8247d2cdb9b253401056e5852e78c2543c61079c0398379b56514a680219da352a426d551195848403928508d05cc3da9b06d3401073c6769b9220064a8ef4034215465da2036a752e56fc1b2b4d005a03412c01909882b9a51c345951dcae21c82b4016d544ec11ad4e08c6b504201ec02b42d007939c4adba5340116a2ec4a9ed624c56b1201b588e05ac4696d2229b67111db20f7cd674c2890f262cd8bdcab325aaeb4014d58433b03499c01044e2b026615785308c2c9046114403c63861e9651cd829694d00418bd43e0b521e79890ec0c43bcd5a4380b421b3d8066cac010925811a66724b4324c9135397ba64019168029ac2f3b8e1505c5d223100ed62c4403570d582d104407c5e54eadd58e94d0052d743336b8099b5b04adad0234d65d1961068c06a44552885b9c4adb2534274c0a376000090000746016f359cb93163e964ded8526950041239db20b91b4064416a5a416b52552d4202cdbcad1db06a54010abe43003641b41b10d8ed803a6220816a48a28300bd59bc932530e8107de6a81c02598ccd280558c58714a9b7611a68020d590eb0136c9ec3354820d9a2f2e8d1e916c4638b3238c5113388d808d2091880da8c14c34500db1bcdad3a534124c0a6a0219ccfb04e662a66330c1319e6190cdd04867806333581199be50450624205403801cde6d5529a008be65ba4f816c27b0d013c2e401ec9101258482404e9ce6d582529a0577669162d2059158ac4c02eb4e76a94d006b75534cd429a764016095d12c148ba84ca96e4ddd29a008c4f349804f64d026b24412b07a3cb0ea0f1f2ea556dc94d002332d7d40d4d870664fe8223ca8b30e120d87296ca3943351c9c1286410cc7262c405691494406c1a8c54a54500fabc9d5b25340105be51494889172eb476c9874a68029aaa
def v3_19 := D 0x19a046b849e71a86138e1478c70524602c2387045d2c93db725340144eaadc81254699404de8e6d734529a00b6b02159d8006ced6af576ae2ab5282d5dac62aed58d46a521a392c351080268ad525636a45b1480dac81005664b45502015a8214d4374a92b04b93a529b3774a627fc014a8704e811023460c53924428c9e344e02622301b4116a2216912b66c94d046b1502da2ca0cd01ce8939368247b9cd5ab04d340088ca5da8566ed01b3766ed91ef16c4d7a36017482ca4596a840585086de6d68d929891700534fe76400e0aa88806a62028aa20880fd1bcdab2534011a7e50d8359694161e72b9405166a0114b31eadd90f547c47a9162046782b298ccc13873b9a574a680215bc90a3cf484c67842013418cc9c0fe64c064ba301b2199e916299234c3cdd2cdbaf200d40118ed513004b34a2e71a4d938d24b9469104a02c03801d658eadb129a0082cfacd17122ccd4164421789735ab7e4a6022edcc4c1a24892034113a51973b7353a53401481004ed04007681c23340c019a050ce8b63a641b429049a89420226b36e6a1a94cfb005b57b46295280948721446e10c50a491280e108806cc6cc3ba095d1ba52ab403c96aae0ecd998366b603a35a0ad1ad859696802b4cf8ba05a8d5033d26819e0140a6415867cfc82d41a419ebb20cf14901f800a4200ba379b564a6802359a5f027a43c12c05a48b5090b3875ab6114a6800e196f6a07b3af23500b46ac89101f5168b48251203ee7572ac81cb6802507f19e83e4cec1e86720f1f38095b147173050f185ba66994a2560221daab6496706e451005322ea74d3a94d005bbb1f11a803835227208104c82d12087280885027715ba54333b4076ad5f42b3af80d982a6911880d12d08c30500dab1dcbb204fd90600a51106e681cd7320675187d068d1206e48281724447b8a0705c48185521f4da90200d824905c119b5509399a846735024e9681109b3088d1904420c413c1242896c14a44a88bc2cb39dba5340150cd63094a317aa400b4316a46166f74aa94cae780219d6e33daad506d4e28368de4db329c8d805c24b4a5310242c4977b3a5964055d68029a6bbb2007055682201e9880a2b51104408e8de56d929853604333ce5728ef209401e8663bc0b101399c0c96532a1966c231f195ba3774a680259bc8a304c4510222252538142c8404b5855ab05cad5b9b202b40105dc876a82703479109a005bc6072e4480fa3795b64fd68022196080d91a216c4f623600f44c1a2036a292035140372eb674c94d09e7029a9a83d94dc0eca6ce5653601b29a83d74d1caba6a0f1d34028e968fd54b16eaa44ef552123aa96a7c54b22e2a440f1521938a8b8eb54546daa1e0ed16b056a9837d34bdde9a673f0d329d869883c21d5d61a5cdac9c7756686b7a3429dd1a665f45322da298bbd01d4168a607f052f0782971eb071c158a1a7e850a0741cd8390a748c0e8d6192ea990f684482ba795b5ce3d60252dc0948bc0484d1b260689b28342c941a05c80cf9a401ed0143ad803e89e6d445006a009176ae40272900b380500e0079175b369d4a68020cbeabf3f615fa5b0af81d857a26c04d2250a5a110b0498ad1dbcba0e0da009693e79844034821532200e8a18e21a261e6952b6c22129500463bc70a3d59209e94104b3a70473600539e9a91086e0660394b1d5b08a5340071cb4989a855892299a052f4b2e76c134d0044439aaa
def v3_20 := D 0x3780676075cc0e54c901ec6b572c921b4d00433a3e210803b4124081a085962024221408c4de966dc3b694d00530166ceec9343277451907540e42eb566e1294c4f3802d422520445cb2d5b9ba0dde9a0540b6813c210077a4523105e5ea11128c1213f4b2e76c1294d045f7971ebd938e3ac9c6ab64e300b27162d8b8b46c035a562c6103c9841a1560b4706027695b35c9a6815029a7683653b17b19d60d8cea46c025a4624620bc68458a51a2427e9d66cd929a009ae53d68134418910f9498441ec9296122d685ecd82529a0065e5a33c72b034b9a7123868f5ba739640165056802daacf40ba66a05ab3cb3439e0d99ceeec88433680370835524cc080c54b94b9d2db88a540148ca4113a300650e256d929a13de0433b5463cd0e43a441da131a7509486324442e912b4222d8a56d7390e5a00b4e8cf586465633a0bd91c70488a53b3473e7692980b49730584a482a2518bb039c8d40333e60314a202da5881da40a3cc916840bacb9d5b6702b4014d55304c6ab32600ae01574016522f46c8734d004197d5e099e2ef00f1770676bb403b12e094aec3ce175ba70ba83085d2a8409b06a660b379b55514a680221da5482532225388972980e19482543210171b98e44bc61e6f156ac94d0043a731deb819d1ce646b5196714bc9100958cc0b1730ae76c12be0da6802d00a8d4004842015288080b1a48789504014046b4e76a2270568025aa89b0235abcb3902009cd1d7467571e71a951300da08a742d110526e72b6bc94d002db2d874fba43505d21c9b570e0d2b8628d005ca8b4a530730caa0b127dcd96e5835175a00a6aba5d802774601392200f489569a84428b26f2a9476fc94c0418b92700da13816c40723608593a809a260248da8248022e92774ac8cb4d008b35815539c1ce8c60d1443063a10134100f511201e74f36ac94d06cb0219d6a20d8b0e2ec1910360d40510095cd204ab26a60139753ba64a680231dcca426d02ea10263501773a59b6c40e9b4014bbc068fb893400b7a46092f508902746f2b6d88d0044321781b50ba35a05c06d02d9b66168d5a0b22d885846c02b9b20158d08136ae694b022b4593126ed65ce99004155600a6a81a82d3984fa0c4c4d064106202625b41244296604d65e8ed929a008ddf2f4803c1cd39a3d100d0f40e76f4103979a5983bf10c0c54a50114f181390d493243de4ee953445015a00b62b80c8d045e426fc52140dd90a0484805b58ba1163660ba810bad4b9db253401136e7e1aa100798ad875b432c45cc4e6ce966dd929a0096b7249813223869400d348064b2304519100b298a212a61eca76ea22943b00463b55b39dc6c4a2e20b05c489202d88426e654b36ea9f4a6802952139e22b04f0af3a44639130094acaa458b427ba56e4a223b4016c40813c202096029c69c3c2b51dcbe2530c0118ec8874e38bbe41c2dd20d4ee886c684202cd1badcb2534012c8e2757a1a30597a8988902eb46f36d88d0045cf9aaa
def v3_21 := D 0x69b07af8383d1c181607a60a404d230490207ae51508b052910c04ef34b6a94d019ab21c9a00386627206488f8a5397b7115d34010ccd690f31b46118a9464c6d10063684f29104094a9144c040ca5022b1b4162ca86de590f69a03d4b549a60f705a09d426a482f1d046c04f12ae756e94d046b029a0968d401ad3402458968809d2cbd9b06d340088ca5ad156a7d41b5056ad34381a34589681d01b3b795a64010bdb4014d3ee3745ba0ba159668e7d17613d8b300b6d5434ad00b5a54523127e60dead846569a00a5da03640748240968414a026f52b66c94d054b0291c23b98c605cc7fa6d63f816b1fb3b48fc05a47d82c23e91b01f28d40af9620552683524c94018a63101a8d61e68edc45680ad005355a1c16ca960d168605a4f402a3a159a0d084cc68316203ee5b1cb852c3c4e965edf929808b6614225109dd1884c28803d1054d5140f4379b564a684fd810ced54473b27428c82906d120b62317b57094a6418045d1c409da010c210042100f61960f0e736ac1294d02a45bb55181b40dc0d654c06caf4af50a41ea8bd0cd45e762a2f302c17963984b274c5e43662f181317881501b480a2600b8175b3a74a6802e59612ff62ff17b06e8346c25be960cf74aff07a57cb9d2bbe2e15c80f08dd1544560b01d80b803de96d129a01b5697619d4ba3ce22c1a400f8994c1316e6b536c9a229500463bda4191ecc6c802c17722480b2e109b3ca9d5ba53400c8d16419036a0c41b30600d882b76c0267062d248990582cbcb5a9d320292b0110cd55b08134b0089c6c124c3600a20126b14f18b051e6f4b6a1294d0043dbd8f0a9cc7774623b0a211d510809a0807a88900f37ab554a6817d810ced5e4920af048402d065a90c5cab5b9b2534010edc2b7a8e5f2b470cd5a3704ad1ca6468e25a346e691a0635c9041ab45e5d1a4120b89d814c50582b276c51940c0b82080560bca230430492825a560a5254446e1966dcea1298377005358b1f74c54cba08a668c1dab11d82d16089acd39db2b7d29a00a5b18262de1d0805a30b5260b63ab9564a680223f90ed3419a003450b012d0a8a814822372b46f6c942df802199d240d8e9406c0dd8a200f44c0405d452c11402eb2f746c94d00432b912a3b988e05cc15bb342527691260b489246a048cb101eecca0d5931838c922034facbd1db0dbd015a00a6a82683478f09a0a7808c03e6978c168d619685c8903e74f2b6d9cd004432d7cab56040da8c696d0cf9b6612d5a4e4100d1624b91cbdd32008e5da00a6a4209a5202ca1010a500ed1ad0e925566c128734d05bba61013324539c11694e0c1ce6060a53001b2940470480c0ca20223996a0f550c997497ba5c40168020abed01b056ae1bf2049dd900782ea44901654213837a9b574a68022995681f12b30b895903c4ac4ce2094d040489680a0133ab597640a3b4012d27c1b524a0a801f4d209382901334c5c059352447402f2af674c94d0030329d0e099d3b04a816d1296222e85e56db129a008b74bac444034595228822036e7536ac94d00499f9aaa
def v3_22 := D 0x1004fb47807dbd5f3cde2c1e6f54ccf78c866c4c332df06193133ce37c00702a51158a94a889acb9daaca8a534016c8205d428b351205d90076610b3ae618502d3977a369b574a680225bcc6941350380da101695036f2f94c2d00433a9dcd994ec0b825105201d73a1d2ac9d44e4e25ced69d29a00c2e534b20a5840b7394ab611f14a6802d6b055aae906d4b4cb68580db37468d805b56902468b128099dbcad32008a1da00a646c5589644b051688bb9d4adb082e9a008d2f2aaee72a2cb8f95ba27374a65a5c07a968c604c07806503365281de0900ee1c2076ca101b219380487cb9dd2a0082b40140ed557b06cc0d34898ab52d08a60a5c5d6e8d92a161e0417f94b40b5c184d8c6c02c697016906c7cc0d546203634cc12ac8b43240bbd9d2cb202feb4014d4cc13410809d02da91396a84478bc9dab04a1cd34116e84c6ce024327078db303c4c9800e34a08a9a407859100f98ea0b8648997479ba511401a8020abed5de3ea41133520811a807aad343aca8b12d0397a59b7364a680f5295a20c8b2206c190b350c825a063f1cc31e36618ea620c71d9063628809cc0567005d1acbdb253401064e621809a10b04b2582e601459308f40940599e58c3c58ad5cbb27ed340118eaab295162cea16dd84529a008a740d0a50064d2003088403d0e5a89c5c4959d32530b40140ed55a5c1b5d6ecd802d2255917518a51690b9d2dbcb2534010f5e62b9b571697728900b94530daa2682d511a5628b25b843505c21982c02781ccf25aa4c621934e48fb9b2dcb05ad175a00a64a079c01044e2b29e6158c93001c48c0595050aa058db952b725340107cf4b7aa4213d61917aa889a3746024a42a34a107928db9b06d30ec010ced614048b0e4a5186c910077d0c7543ea4627492f6a94d00acf219d25515482266a42a25420685a16d25ccb685a65b38332d98c996cb348b64064495c5503d91a80aa9500184681b1ad30d891986c3348360464096742b3682e966dcd929a0071e53000048c003a340b79ace5c98b1f4b26f6c2934a68029db809c9b714477f9e71a61d38dfc5881ba14403403801d45ecd42529a00832fa1f62b50f80da87b96d03d1b661e1db20d40a886446c03c975016a588139422f5ac992204478b376e72b4c96a0ad00535582cb08cd248402b07303d2dcb9b253401147c875e786760401384e88983cc2461a522101651a50f34ea76c1a94d0042f3da8682660b411aa18a9003ac6c858b4a9b7360d4a6168021d29b19914c34c8a59a4419191a294c98878648455b2321acd382926981483c801816302eb49458916e7356ac22944b02a05b418011ab80b9c5ba74e2dc0a2012089601117526f6ac1294d0041f7d2900daaa82ecd2a83467095b2380ad8aa376c15113401eb8c1a103548b22416c1807e6adcc99298740a9668e4a90c9d246239ac1127090809584a2e08b6379b564a68020e788df79e8654b20b2859248c03d8658390d2dbb2514dda008b755214a8416ca6f6bc1a34a6802daaa
def v3_23 := D 0x38b1e73c6c139e28798f1a04c6950232f50111dd279c69f84e3741e61c64130e3009452b74606411285300885424dd8e56db929a00b3749202e52349a19168d0121464026b4801255a10404e1cee965c369a0034e5301a44600cba0d2db25342a3c086750691205905a104a02e6f4b36c89bf68025a13609965904c70cb6217e9910c46d8465864203583981e1ce6d5929a00878e43ad742b35ea0d982d161825a0b82409d3cad9b2340a81058e6261412449068089d2cb9db25340299ca60c8347ed63a0f684d07b37e43d93b20179800e648401e34b672ee94d0043fb922e0da91696d08a9b66451db2099456448f464888b486d2e5d6990046e6d005355a18133262088ea28ce3508a70134b15a16170e72b6c1a94d0045ba0359a18546d442934a08a1b4012bc24c90f5168b302431f64a973b7114a8016994c04933b02009dd5600eeaa846755003340a19d24b6ce6a9a072814f381310d10752b735694a67d802d2d8e8d0ba246426963003091809110078688220272eb66bc1b4d02a05b57d4e314bac98a5a44c01e692b3122e486e8d90e69a03d4b5a1067407391499216e92774c9a94d00503b4ac05ce4a02c208a59884e0c404cf1039330c07b1d2cbdba53401130e74583d46acd5aec10d4bb9964426859a44169662b84544a4c4a242ad4e9ee5904a6d004a07d73a020c9d01b6ce4250a621211380b104a411211f0b366a2e34a681502daab6dbe7af00139a4608cbbf04476d1671b40d30db27946d804a36b9e41b599205e4e8c6d52c40728a20370014bb161009bc9d2db2ca5340142ea90594246d4202c2a1086e49e96db929a03b66b040da58256cac023600f48952858aa8442a9506d1d6e8d929a0089d728c17324ae51922704c92b006495462246b39885a24651a966016a528138aca40991164e0de5552d69a0540b692893418e858805898b412c8c60b51117a37b9564a6802575cb849cf481027a2c813c70619c95204c5be8a50de4d200f30c9a6172ca774c2280b500463b4e17462700a200b4114c20a88898b9daaa5340eac08675e10247e0432278a091127744026a1295822de0ed5529a00e26453a2b8ab515a0da8ac06d0561b662addb20b40b085a35645502a22ad1b00ac8880aa36205d3282d244492202cbdacb9d32008292c014d503994a00e922d4242e85ee57129a007965aa41231040f68414c3450501f73a9b564a681502ffcc5b81a3a7869402af144a568b30d04974a973b6114a618045933a99e1ba00f0dc80686d9c3137079c1b700e035c380385b0d1dcb4ee202b4016d4935ab044035967ceb3b1a0d9ca65a8c0eab4729835a03a0ad4930d44442aa2cb8fb0b2c4d830e02c2b4a55173d9a803ef502c7268008233090415803e5482c77642b4cd1173c5882f9a4acd48b1378ab574a6802b9956e099abf04ad5c0246b15d18099c1ae609acd82d5d3111b5b9a3764a681678110ed21e13888509802284807b92301378d0c92e45a462716ac6ec94c20380231de8b39d7528ce01490aa55bb852d29a008b75582ca1201e5480b0b042403f2b566ec94d0049ab9aaa
def v3_24 := D 0x1b8623bb9209decd04ce928233bb4f38d4229c6e900e3740061472608dcea040a8868839c3cadb06a5340138ec7d46a00e0d489c82041320b44821ca0221409d45cee990cced004b58500cac89670040138b2098858f14402c812a4822d8945cedc2529a00835fa5f253103135c7443470f3ab595c465681502da2602024490048098cbad1db945d29a00a440142909002c1272a966a94c9e381502da7406e13901709c60b003d246881cd6150926230071f73a59b6c4a680b1976809c79214c1e64a51e4451009058b00b0b4395b5094a68021f3e8bd04f4674660334d301986940c6648064ba301af51518b1e289d2cdbaa00d12c010ced50a705a40c833182858807cde724b4325c9922f46b36ec922d00443301922b80b21582d6c52a585cadbd1b25340bdc540b6a720d5d2e04aea11f615059a009a2d27a82c48f783a95b70d4a6800ebc95e958ce4035471c12a3513b498e05a4a582c24c91a80fa41e7575080f26e756b2d8827b68029a52a09d886048c44b4400eb18b0f30a76ec12b4a68020a7eae15ced71b674b8803a5c259cae02ce16f8a70b78b305ba0982dc6ca16d8250b727205b66902da2c416c8a203a30159c3803e5cead53529a00ba7694c99e2c73ce0082a711841280933cb1878b3a56976e14a680231dddc0b675b0ec4e8034351019931a0c8f5a6683ac9331d61d9011252a72011a15272b4e76dc1b4c045320091a800308402a51010164878950401403eae774a80a2df8025aab5616720401393d62888390a54814590abd9b04a534017ecb4daaa72089d181ee28802054202682081351121404ce12e55929a054086764d65262c5d39b4adb8ecd29a00a4708ee631817301c0b19b59da4d182d20341614288d40c9962045d9941ab2638c922034dabd1dcb6202b4014d5f854e7050231824110c1088404d045435110f9ab57364a6800c790ceb424cf5a0c678d04f390780d690174c6572c9280b4c046bb2b09b40b2a4098d405dce966d860e81d368029daa0b876f0581dd82b00f1864cf1b489033187a33674eb36d89500413790aae90054742016832d4862e56dce9929a0088af03b55974333cae7985f694201e1961c69032b09c1cadae06a340110ebcb8c800f8c40040120794f883c914402c81284822e0de6d5929876008a7656136816548131b00bd1bcadb25340129be7e10676070ae4e40a991ec65572c9294d00f25a4a633d25099e1273ce0082270490f3023e49811a04a063123045c51013344a78c4428f17ab55594a680231da93514302349aa0b048243746f2b6c94d004a9b95180d9a8b04cd4702b0a34518095c487462c88426c521476e94c9c3021998800347244fb08fe8d447e44a0252b31d00916989c2d4b9db86a530c018cf1e0ceb4f8e70040138e3678c5cd24602c23821e6948ed9a529a00a274d62d291ab058926f2b476c4534a68029aaa
def v3_25 := D 0x38203d9a681e905a4d6a49db5198b14a539b73965b64099b4012c858dd08f82e84759a39085d804d5693a02a2c49312973ab711d1a68029acf8673659338020c9c03807003bc8a9db4ea5340122ea2c4ac0b22b148b805dce96d529a00c3eb482c7502c80b4655017a37b956375d34010cc96504e9d91e42ec4d21760e8cbaf84442e8a41ea0a103d946cdd929876004465b009144404c2100b5114295043c5caad46172a94d005b684161e72b943c404a3d1c331e885880bc4e064b298619b08c6e5ce96d929a0087ef23181b518d2da0c936cc64a36012d9300b4b49900e3490c402c4a7ba37954010568029aa7680d881c28c4944179068b14a54484fd3acd9b253402c7ca6123b200705889403480b4412a203746f72ac94d0049f7992036e353da710200b8d4e41c426abbc1254597204d68a5cedda529a00a4632a704795303f6b941eb54a0fd36407e51203f07881f7544045c3133170f29ab350d405a68089da10a59a54b1ceea1ca520f31930ee72b74c9a22872d005a36816c6681d98da56459882b0135cc0e54c901e4e74b72e934d0043334b80ce62a1a400abb9459716e514b6d32229500463a68dd51a784881a346201eb7a41646952e5080b086d65ced78369a00a41606e40901720572c882a96c014cb500a25900d6a588105ab44ac500909b175a3b6f140568029aa89e0246ed0938d7ac9003e18a39898287a54dba88a534010f5f63882ea9459a88e0ec803b28859d732a28169cbb52cd9bba534010e7e6aeac98d7404a6b992320f4828e4aa30144d8aae5d90f69a004465a5c81b546c1d9a35068cba836475c1b14691d82333ac1193b608c40b0460d5022f26811282b03314c04922a4822274b366ec94d0041279a7500c8e1e26a30e92500ebbc069a82cb90065e94de6db929806d652ddc1396ec798b7504c5bb0652dd4d296e858cb730465b902102340161d4803e5cee9529a00ba60769993daccb8ad665036b3240b59912da4c736cc35aa1a523d00d148c49b279ba54345eab4014b3504ecea824674da200758c587a85b75114a68020a7e88c06c8458362229db0076a4a102d6a90b06017ab379264a61d0210fcd560596400ef38ba8c6972644734586e8de56db1a0082ee4325d01331b4a9c8b704c5f70a201301900e8716b2d94d02a0433b51c3cd28d806946a12925889004d06d0394d1dae06a1cb401697b02d0bd00e85e40342f0f3617701b0bb0ee61ec1732ea3b195e058cba06d45cc16a2e41b114b0588b8b7625c1cb12df3b496e4aa4b6c3525b01692d70949005a443c4b224e02a82588d4188a8d7254a2a8347173ab595c46568029a41742016405b40900bb94ad9d3a2abda00953a2d4809c1127505aa11043c04612b46f6e94d09cf029955a647034a8b12483a0370e6b56c2295005e316bcf4674200f002b431007b1d24db25340114ed174bac40916548a02746f72ac997a6802199aaa
def v3_26 := D 0x65a0ceee88277bc0333dde099e7c5866a6aa33531a080f80d690166f2b6a1a94d0046ba3e610803a88b04a821e2854736e13a294d005b59b4ce2c900300b41d40e84f56adc94d00424bd3c80d998506c9391f629c42b14e00d8a6f02c53723601f1494e2c8890a4d5e52e8dd29a008be5340b0169c964d064a16201e282d84b22a0296445c68de6d5d29a008dc72e7d73a73c51d22b34e9ce8074e71b390b648cb9c3ce02dca50231814890168772abc294d02a05b4f524a27a12100b43156548c3e94edd529a0089a633be5862b03aa6c72a24b0f95ab7364a6824f87a968c80cf475c87a3a873b1d241d8e80ce87396701b06963101a3de8ee552500415a00b6aabd3d6a6e41b5054c28202c490680901734ba956437d85eda00a444827a74413511269e1d134d03b82541dcd220da4cb06a131eae2756c1294d0041bfdaa61678210733a9b39cd406cc698c252173192262e5d4ee993710e5a00b4ee81687700743b601a1da19b0ec80d876002c27535592c06acd286d464656a3aebb115e95888086b41e815a34b3b499105a4ebb6c257816127415412c96a080cd101ea5882d3d24d4ab529ea121a6e8ede5712a5a00a6ac80362c38bb0b230d81bb04a0dd8a20169838405a960391402f26f634ae94d0046c39624f9eb1100f588027236c11141e79c30f2c40728a201e01b1802e696cd56529a00af7695e515c8974e2283a612b931858ee8c42f144036913152d08c60a4c68ded5929a047e0463ba8c16ce8a1b92fe05c8e90343d919a0ec64cc76276403e17255240b842a4e25ce96df929808a640927660442b30200d980f02cc06bb640385b101a8d807a6052096248050808bb2dcb9b2533ec014d54860132d64f986ae74c35b3a10136015a16803cca926d929a008e068bb14c1758a40d44510482283b20132a15645b2a8945a42e6f36cac8bad0043332407dd0080ae9591f6cac60b604b5693875a2c493a5379b6271a53401481f08c4080a6231a529080910a1f44c077ca501b2694834643499d3dcaa00d3403c96d6196dc57502e3848d88c1ea8404e68c5900d5266a2c161101f7953ab60d4a68010dc8cb0469a58222d7cd180220840494054b005a8b39db25340118fd17698a1b92da05c8aa3b220ed2d18b5a95c352d4582cfc3ac9db06a5401048e7bab6e2f0017136c0a8f742ec3b99661dc91200d5d60448b2a402136295a7b7694a6808590e529807194a03802401be510099c4acc88b31b975a740139680219daacce0da0a0058f332f3382d699cca6cce643264366901c41313009acd59bb253400c4ca5ef067c81c33d7baf9e3dc60f1eda676f6a43b7861993c030c97e1e7026661d4ed82861a94d005b5093ca67eca713c5b309af2985089ca270ca513d67209c06904c62c42624a202b4014b9586d20172897ba64a0f1b40174e94705d0a302d8514a732880b594305c4a133405049982801c40896c50a585d4b9dab04a530e916cd5be968c0e8b8b9a06d4564570d806c2255ceae12995570052a99fb4420f9a2a57eb15226e6a7e5735472b1aa43dc14f82e0a8c160139c22766c088f73a59b6315a534014d264f3087269042034201cf8a1921cc344c4e6a15cedc44352a008c779a1261ccd728e640940f49660719231cc4510e6078472f542046d3499350b335318b9d2dcbb2534012cae56a4c30596a84d0902ee74b36d88d0045d39aaa
def v3_27 := D 0x6e92ce4080a73ba0b318dc498d1d6485e29671735138e1c79871044c2949a402ad91562d243ea5ced44529a00a5e5b22833a03ac3272a40c8f6a539b649d14a6802d95b94a9716a76d24ee94c4ff41802d51219da880ce811167004153850e59828534c08b8250124d20505088098e65630c98f275ba54d4a68020abed65706d0b502b58fe2a9caccd4e5505872a272388e691ca60c8e5242444e0b01e30a602e01727953ba74a68015194bb706c9db0362ed01b007a4122091b50829450421ba759b364a6802247cca4d67684c58f95a37b6a531b4016ccc8764e0113261ec4128f60f887af64402f20a1ccc0683e9cee552469a008a9fa43436b2100b59100dc45882e240416121e7d810e3cc07c8350324198139c0c786b07932098d9ad3cdb6200c0118cd568204c74c9671a60d38d100986972c62943a301a0a16034172ac76edc94d005bba901f740202ba42d1ecc8b2b4012c5e1290f30598125d65e8ed894694d005355200d40ced048cb4e360128c5e2ade5712a585a00b5060e76069a8ac91254116272f0a76ca21a94d005b57d01b5be71d1df21a8d4a4b477c64a30e24d15f09d66f7acb2974159bdc82c8ad6f03952e407ac9559bba53143e00a54c8276cd03336640998a90cac4182562a5619106a8c88518a042b4102701ad202e5d4ed52529a008d76982094c6654c00daa4007db0841ea8405bcc5223e30f15ba754a68020ef98ef6c07a3b582c0ee0158078522b22e310a8455a436f2b476c95004137508a0d983b06ac2206e20c817105e0ac8430ec0128b101ea1cd8924a9193585da4d6adb1095808866aada261f6d000f7678e67b3a433d9a1996cc30c8c50a23a18f30a44488098870d5a92c88bcba9daf2886d34016c7c44807c42100b682481035682165880908850271a579b60eda534076cd6042b3b000d9a0276cabf8b628091b00ba262512ea09221411765b97364a6273c014a5156a1294b4094a1984a28c825006202d30a1d4b0a83e5ed68d929a0084ff358d07730920b980e058f19ced38c8169a1c0b0e3146a046a310234809a60349d420886c6407d5e4eadb104eed0052dfe33a5ac09d0fb7468e28a722bc9196fc79c15044c03d2520d2a4284464e90e56d93b694d02a05b4dc96800e87889a06d44e4510d406dce96e5929a008d1f3e0d62bf04015f810c8de18246f04122b86f8c06d46543c1bdaaa5341c3c08a744f827a29d93014cc940a55420265131d9114c3e90ee5d9006a0083f633b559c073b034d8a24b0b975a3b61e186a534016a795da90d02d442c35a1986ad2ad9da54882d2fd27610e32b08a66d64409ab29f8b684b40b43f33d806bcac03b93520986accc66840da9cbdd3200feb4014d4d4163a3e53151a058a8c0eb45b415aa773b487675a69d3ac34e5b59390eacd3b2dc03b02e14e8160a727ac1c805607f378d20b46b0c9722d081fa795b5ce43d602925e0d919b06c4be83322f811133ced819774c0d63a506add2035458809c1251040d62123905295141809da5ece89d298740a166ac88b60f2c9a0788c903c41442e60b101712a46962954c326b294e76e94d00429f956a099abd04c95a9a62b109385862982c204a1611a40b049101168d3404dac95314eb61a9a9019ab9b7a25431bd340174ed0b4139908098c2b04441c8344105d49439db86a530108eca75650278508123ea2b0c83dd652e2c59329bdb7253400c7cb5128d29221618926b526f6c94d0046079aaa
def v3_28 := D 0x65a0cef77026797832ba8008c84d6052a4059bcad5b24a5340114ec7d44800ed48248103d6822d5080908850275a379b60d4a680ed9acb236088c188059c5c766c570f957a3b64a680227bca697cd134026899c12c4c009d2620488ef0a727805212fc89c18044804d342092954d44888bbacdd1b25306ee0540b6b230e760aa520054d847125810f4a39b51e1f8a534016b950d61ca02b0e4c150726ea404b58ba148d1c3560ba81421fa795b36a681502d99a77cb400743c44d036a2722886a036e74b36c94d004a5b9d422d96a916c4dfa3600f4824620b6a10528d121374b36e6c94d0b3b0291a819e8d304d4693c781f253c0b669d8b634cc3c424216451915889c0ab84205533289262ca5ee8d82500415a00b6a82203598ec9a805cc1a7324068f695a7b374680212390cc0f3c86071442974d2181a010c0c58646bc2229711201ab08808ad25682c48f51b7354a61d80f52daa31e79521b39a5f094874244426231e445b1cadaf0e21cb40169a505b0e606565d016a0707d08b70644ea3b201b9850e3cc90684d5e8ee5b015a008666ab0845692c12b02471401a44a02503501d049ee95d2955a00ae7408027cc0403e600f9e2ff60f17f0664bf4c325f879c2fb00e060c2102650158a5803de54ed5643529a00b6954cd001c445b248a20a5898d39cdaba530108ecb67ae83d265dd5132e8c403aeb0488607a762bd28b2a414a246817acb9d5b4ad3401280626a0021250004920002a8c04c5251016b53aa5e4448504813cbd592a530e8af4ad55a7e573d3c0b5ea145c4f6a310127a8a005a72a888202e2eb4736fa294d0053100dab87e695c3e0dc88d02e44621910b1d269498109a1d42624fb1bcdab04a2eb4014d58013b034091d1474ea463a4545113891889006d0823d448087ab159bb253137d0600b50c86744e012a43039c93914c463227084d1280d1340720886a02674b36b894d02a08bb58593b2c2a0d96149ec7098b63848db00b6b124101a35629088901b975ba364a6856181485d04682eba52d3553007808ac110b68495b643da68028dd958a4a259522242822f2eb476c30b4a68029dae0b91b2064416a5a2e0b2a96a0b205d6a5ced8351a00855721ac1b50d20da06a05ac34bb6417c5b10be8d805624203d738c12885932240bdcad39b21e82b0e814d5036048f31c651904928c80c9004b165982c58d24dbb250bfda008875ea8676f3833a3160990c684e07f4260f50f10427084079445129410f9675b360d4a61d8289da7e03673d81339bc0ad4cd046a6882334141580d82c87202c20f8639a2b74a61c58114cb312ac8b32c528b485e8d66dd929a0096bf2a3407683500f629a3b6c0d4056802daadbbfd96d81ecb6a8d403b567208207ad161d2028280fb8ad9d32140da0094a5cac6721daa38ee951c886a4e3c25252c1600da44a3c754224e8ded65b10c46d00530972842e2e50a9cedccbe1a94d005baccab4d060da7250ac75083624aa2a9044cd4a0f1a84080b43c91399e46b4cdeb3667911933c866917d8ec8ca98aa01e23519d12a0b0c8d06595a62f523313026907d28c816cf2566645d29dbcb253400f7ca57824e5c8091eb250e76e6034a68029aaa
def v3_29 := D 0xd3e0d8e9c46c0168b924cba8ac9294c5d925eacdd29a00a665249c9a0033662e835b18c915c4169b5a93b764a680233bcc06852903355a78c5468f892ba364a61680792d508ed9a838ec9411b647845b13028d805c1631040d0a405a3450601fba594364a4dbc0a814d64f1a8ebacb4793a7597620acd735681d823101b27520d5ac64b9a101a6e55ee8d92995ff0052d646b45e40da02a6881442d12d14022284dad59bcb204fc15a00a69faec801c1551100d4c40515441101fa379b56097d34010ccb359516903cc9564d15a9807e98dee55d29a0096af240813d16209e10004a4580242410f381f8c9806c8d03b24c407d40abdcb86a00d40118ed568830fb44807ba20035d0c19968230c8970a23a18f30d0401851a24409742102a8700b14262ea76bc121b4d005a5c487164420f9735ab64ffa534014c058a31020c98a1c44c01dcd2b45c347a0c95d1ba1cd3403c969f505ccf7cac66e417132c0b4a0205842cf0c89b403d39032886b4407dce56e9b102f6d005341841115201145eb24a2f52a101291a90f504366ee94c2d0045ba84473b532399b359ce59a96701291890ea90f66c477514a6802d8dcd0e34cd41f314ae76e4af0d4a6802d5ea43972a1079c14adb3486d34010ce83804f01b82620d812106a48404ad8517305cadd1b32512b0106ac876aad90f9eec700f7631670c3cb103ea28805988751ab376594a6802ddd8de09d46554e63d8a301445108f4a8405d045435110f59ab7364a6801d190ced5e9eb53720da82a6141016248340480ba1dd4ab21c85eda00a524876a044375490fda2477dd1233e689156744566ba24462d121b0e89098344909d9a474dcd232666914a734560b9a4492cd21c8e690a43347e1d920f0dc8810d341f099a482dd8a406dc51f9f6083cf7020515007c5680e4d2cb9db050d29a00a684582a38a558805bd1ab181a5ea0d168d01ba3759b60d4a68010fc81f08c4080a62336529080910a8a38c12a22603b652808291008c86d190ba3b795401a6801c796d3525a003ad0f11340f2b51391443501f375a9b64d56802347cee004e4df0223bfcf38d4289c1bf14402c0e2a9803878b9559b04a534010caf44fa6d627816b13a1d909c0cc818033426c37112e0b889a3ec049235023c998118fc40bae0c384642c82c2ef2b476c1a80ad004335590c199036ac954ad1610a938529ab7384a6021db94c8110ac80803647ac5b13428d804d1702917505900a10bb2cdb9b2534125c0a6a5809948044c295a631475118a54788529544034a386945cabd9a86a5320c044e99902d4cc00ea65c03532c05a1954eb0ca015864c7731a60b99921d8cc882c664036a2980b518f0d88c702c4635bb1318e589876d84c24d425f21a12d80b096b8484b30d325765992a4b4894a9644a217604f84b0316f5418a46a04f2d2019659024c5a41089a205d4b103c614817308424b6933c8606548e824512d684d7cad1dae0482b4014d0972842e2d89ced59a529a008a753a456359368c55c32f2eb476c94c0447b5a50825324033890a09c43e04c216023007df0848008407c4a63910b1878d29dbb2534011698ef4868e5da0a73d1e22940129404e46643931d5cb6253400f7cb4d62d343b46ac1625a0736f2b476c94d009a729aaa
def v3_30 := D 0x6f75cf379807850c11adfb19c30f50402ca43c1bcdab28a5340116ec7f24400ea4295082dc4a966dfb4529a00b602215981006ce8ebb654751b009a262512ea092214117659b7364a627dc01498804e93d02329e41114ea09c20f04202cb411c2d4443dce2e55929a00866b7696414b0816e72956caf7f14a6802d7500d9ba78ec9d30564bac1b274a05916716c4b123601eb81489164028426b374e6c94d0483029a7cbb20070554440353101455104407e8de56d825f4d00469f91eb83872a607d4945b9b84ad29a03d4b463027a31a53c01c0960e71cec73967017269499024349b9d5cae20082b4016d558016c40daba24cb1aada294c5caa6dcd929a01626530781b483afd541b7aa92eb3550718aa690331210188a0d8534974d9a1af0cc8d756a05d75b252aca96124e965ecd929a093e05353484a57902e06bc160079c72272cb342644ca21c7d68dee5b1027ed005231813e3d539a1e900d0f40e764b01233ce5981e610c0974a500ecf1813650a4d6341ed2774b82280ad005b4a260202da29608a017a5973b64a68021dfcb053acd7e0366bb83ab5c20559280d687982b444a2a91c00d48530d640a02b2cb8fb0608ed830e02c196af50ba06a8658cd432b02a16a3d40ca89a00200cc23f05600f8d2049dd9002cd440511620cd222a9442e8e1e6d5d29a009c669360b5ca205aa5a4b432cc1999640c885b2a51854591bcd2dbe234012fca7b33675d94b39020c9c9a104a581227067e5280d708a847221f06b72b894d002db2d03f19d01004e80f0074075b39038e1c81b3ce03423821e2549ecdda529a0540b6aad700da6b726c016911a48ba8451a9485e5ced69929a0087b731893b58c20dac6096d22f9b67179db20b945674c3c911165c5ee69590f575a00a6ad339dd6838ed15827759c03b092a5296e6e14b4a641802d41241016404840480bcbad1db116d29a00a6b10b6e38802715d60b8e1f71c4257781c20b2e409a94bd1db9b5d29a00a5b69f52db22a96c8cd4b6b52a5b69722db26916c8ec8b6b4245b52b50da919015a2cad058b95ab7364a6804eb94cbd26b497a84c593a5937b6114a802091cdc64cf3baa879c7923b62809d9b8546b819e71a7dd38dfe01c19d28437f28202a81a80e26f6aa1294d00573a19813d104c9808134a04032401fd9100b9c4acc88b4a5b9377401a5580219daacce79861e9440168c2b4582e8e5c56df0251a008874080a60f241287ac6900397293ba6401a6802f9da8682634399200558d68b1683536ec2294c300443a5717382b729c15a2cc0acca60560b282af2941569c80aa8240550b102a72880a9c651eca32a4f0cdb4bdd2e200b40174ed169a1c0b1625a07805dceea559049ed004a63c13555419d9c25469549e70a7dd3853628806b6255a445d09bdab04a5340152ec41c1ac8eacd443c34a01f14bad27698685c5890e6ce96e5d9285ff004632b1c91803b18a5a30b5a13b764a685978116eaa4295082d4e89ed931e1a34a6802daaa
def v3_31 := D 0x37d82727e8111dfe79c69374e0fd8a201602960051702af66c1294d00431bd91c351b82968dc013440f2a460964d0890272e774ac94ca3380298d42a52199511b50c9003ac62c3a428db9b86d2ab4010cea8b2ea00e0448121c8041280bcb9d2db0dee9a0096b2f027a27412aca209c5f90441060210164614804983c60a6d43529808a48757b836607480d2968411a926f52b66c9502a0417f9949aced098b1f2b46f6c234d005b32ae0a54c0b928ba364a2abb403c9681f8ce808027448233223f0990c614e48f0a6245913823a898088868c884444e55ecd445e94d02a05b55a9033bd46099e5d0cac9a8252135814a9016f30b6b894d00453b0c1d2858ee8c42f14401e8829d354501498b9d5ab2534198c08676ab409a55a34b2aa0277558123a20e9d512748aa90a73441138a2489009c17411169582ba88921b5ba3754a60dda0c016a05048c628244089d18040a840492a2026a042a890173248b9574a68150229dac02fba60019d175b2e97fd874bfc3d9a101ccefe86e57f0672ade6b95fb31c8121ab45a55a019b24a08b091f4b2e76c6c74a680294be0908e90445311a403ac51009014b0128b56b7354a61d802bdda4b02c31701281ee6cc428162027179c92d0c172648b9d2dcbb25078e008c674683d26b1d51ec28d43ba9620269012c80695529d6d4208858440ad8de56e9d064ed004a13413507c99d8207ce025be6012893001a49004774603d8a283a930513615ab76e4a2560221daab710675b84339d4339c01014e3702e50c981280d480acd4c01f42b2f6c9a94d004167d526b4a6a13162498c2d3db08a534076cd61413bafa09957d34aabd02455e8d11b0888806c1643b05690792b39db2534013bc835fa5d013d46c1999a554e52f1e60975d304b809425b14412d2a102348c0f508901e6972aa8cb4d00433b424013a11e08d63f3ce6b78273431d19c7c79c63244c03c45291428829384395b6e4a6800af96b740ecd6d03665501b22a8ed884b48c1a5638684588d49b695b354a81502091cd39a3749c80ba4e266801da2b2c2b60b41161684db9d2cdb293d29a02c66e21230075594a8b16750b6ec94717680229d49a524345951dbcb2548082b4016d567404c71a2a5005870841ea8404a98515305c0bdd2b25340108dc874110232061ab4f04a8d1e972b46c94d02a0f25b52305c4b802a34d9528a7b29004de04024b9008809952cdbb725320842c9450cf02532606fdb28342c941be5c80de9a401ad01662d803e165ee9845006a0082cfb5740b380cf08402a46243a0bc29db852c3529a00b5672f68b340b45980b62cb0ec8420344388151594cd02c9266044b62852c2c56a4dedd6529808b66886c941b5668016f34d0cb2e4c4b44c5e56acdd846a0082ee632b30133a6609514604681ed489cb34223e849e56df0269a008b750490092024240274b26f6c94d00460b9aaa
def v3 : BT CertNode := BN (BN (BN (BN (BN (v3_0) (v3_1)) (BN (v3_2) (v3_3))) (BN (BN (v3_4) (v3_5)) (BN (v3_6) (v3_7)))) (BN (BN (BN (v3_8) (v3_9)) (BN (v3_10) (v3_11))) (BN (BN (v3_12) (v3_13)) (BN (v3_14) (v3_15))))) (BN (BN (BN (BN (v3_16) (v3_17)) (BN (v3_18) (v3_19))) (BN (BN (v3_20) (v3_21)) (BN (v3_22) (v3_23)))) (BN (BN (BN (v3_24) (v3_25)) (BN (v3_26) (v3_27))) (BN (BN (v3_28) (v3_29)) (BN (v3_30) (v3_31)))))
def v4_0 := D 0x2e448c019b97a354a6802749c963561d6de510f469ed005238d387a3b595412782b4014d123521d5eacd54529a00657247803021c51011d00808e20204704080b2b4e76a94d004d2f98dc86440601c00f4ead72c9ab22d00520d43220336b34e6c80b4d00e33513205a05982900b1cb8ec08991c4ce9e56db106bec04a58d587ba6359640512db4014c95a273669a626fc01489074a80cad0bdcb6200aebe00a68b1ab0ea6572ec834f68022191dc69181934a59551a60ddc014c5140343632948293b594215a1cb4014a23221e9ece498252987483ef35452ab7364a680a1194923521eacd655014fd6d005310e56d529a00a0e8b22d4f300334736aa1294d02a1ff9a21cad5b129d29a00a4b2e76a94d004ce79941d40e8634b6d812d0030329529da2a512c00c4ca6a507503b9d5cab24d6da009552d66a94d00533298e3825406568ed0452a0090af229b3a5d1a6802819a01248c1fa44201483481ea48ed529a00a3f7252b744a6800f38ccca0ea07385b4ce463ff814a83a81e5ed695007f5a00a6aa2993dcb25341c7c0a4b4006659cb302ca8900395ab740a1a534042cc58d58753ab754a688bc0149a4d6e9b109580a966908ba540631c30eeb7298932368029538dcab21ed40118ce6360694019b95a3764a3b7c0118c880284802e1e4acd8352987454a66a04e09415484401623621de8565529a00a7472739b554a61d21d396cc80c8078237b96494a641029910a294084148016c32c1c5ecd0252987482df3400e0071ba7596418b89dda00a4e76a894d00573328e2d41c2d45e0edb0251d600a40a3e400656a6d9528958083373549573b54a6802465c843441e8ee511c060ad00531d688ed9a529a00a421a20f4a76f2c81470568029a3952948193495b5c496fb4014a0e2901c2d661cedb10b1f004b1b184a40cc8d9d2e689cb401483000b00cbb51acb22dec15a00a6a2a09da84a0cfda00a462c56a1294c046b329ed5129a00909f2195128032eb3566c1a9535006334359d180380d8079753b54a68028d7cb23321c5ee6171004edf005318f48880ca4d1dae2340bdc0a5359498b16c6b2f6c2934018025aaa
def v4_1 := D 0x1c609401c46c43ad1cbaa534013abe4e74a894d0051839146143b9acda84a53412ffe69356c6a1b4c046a332369a254a6020fd9acc531b754a6827ef96c803801ca5ee95004ad6d005350c38c1c69ee57107a6d005280d8077ab5954a68026f7cc573b44a6802837c89a54a04dca400a5966dd79299f42166930c476c1a94c04353900e9998195a73b5641a534014c92ba354a680409948c6e5d69d004e448700535472ba554a61e7c0237e471a70f4a76f2c8e73056802980232427b9d193da2889e044c0253171d4b15c3e96cdd529a021c652144111032874b36c1a94d007679a41a89401972ab55e4199b40149e50ed4452a0f0e05306c04440c83481cdee55529a009057210512803340b1880b873ab960d4010580319a94b2e76c94c048ab549d92253011ebcd665165a82c5c51bda8886d30c014c87c0c800c8acbdae200c01059e68e7572ac94d002a710fc963561dd4ee9529a00987f31a35a1cdee51283c7002d32902009501ac62c3cb2dd1b06a0292b010cd545ba33314609582c165602c5a945baf200d4036c963161dce16d792980829f2a8ca879853b5e0d05a60299a4263998a61444e592200e91ab522e5e8ed546569a00a46b3e30065e4ec952987408d66372195018c70c3d3ab5cb23edf55a00a4eb2756cb8b40568029a811c10f2756984a7a680292a08d401807003b9d58ab236bda0096507503cad9e721eb014865948420ca100a11c10ee52756d84b30568029a52dcbaa5340149de52b46894d0050b299674b2a94c18307929559bcaa02b400f2ca6a961960eae768134d0048cb900209515b348800ba340eb214ead2251f2b66ea94d07d702983e22401f1508052e32b6a1a94d006c3915a19589704a82282220e5ce96e5b015a008b6683d82583281230550d5073785b54a68022d9c94acdd529a009977316cdd299eef0045b288c8874859b36594a680af94d47141220350d507975ab5ce099b401493700cc9b16600a5668dd428694d017b31c274a8e0ca520a526ce970afe72d00521bc908032c74f72c803004247319a309add3474d0a26d0052a3692b64a602355931930ea8272f6f3a14b401802900ef9a00660d003a66601a4330932b4e6a1434a68029aaa
def v4_2 := D 0xba341585110532e6b4a94d04930294c2db9b2534045aca43b02520660e6d579298548b669356e6a1b4d00433251b7354a680269dcc835b954a687e9858c9a35a1ee8da5500415808d66a3151dcb624f1da00a42f74aa94d004dd7992ae276c94d0050579286283d2b9daf25301121e6941d40e8634b6c22135003132918d29881973ba59640c3b40a814cb3659545d6807929044095819715ba360d4a6815e59aa5d0b4aa48d301084e44912500660dee55b92989060530b684a4128a220a49ee55424f645a00a45b4a20065066ce9b05ced004333483416103850a42a0b59873b6c42dbc01288804cc05ba100a5c6cd951a008f270332856de5929a009f0f20ecf300330e64b6d32950073329a952f66a94d137302928089413c044014ca38dd3253407ac832731ca84a40c23821da8ee571205ed0052a85b7364a60211db8cd003801da8ee5712426d0052637b9564a6802611cca9b7354a610180d9ca528ad6ec2ef401558029aa947692ac944b0032f293e0598019a75b4187a5340065e43f2240074816a10166b7299c827b6029a198a88819293644a6099791ac8ea6d129a0087c730412a2822e8ee50af6875b680290ae194019ba537964056802f99a9051e300249180532ea76a94d005132362b95432dd3011acc38d3878b5940d4a64100a7c8882cac4382540b11910f2e7564d88c3a054b340d01210322c56836f4a6022991d69998e800cc031e600e655a8d461e94c058b31ab4cccd54e626a50313505981a710c02ccb9b2a957d175a00a40c00680731930f47728b6b40568029aa1e6c90019925a3764a68029f9c8d6e5129a008fa731e000b00ce34e1de6ce971212ed00525ab97360da68019ad9a007003a9bda7068e9a00a405b6103c6508052e834894d0413b0abcc739b557b3d340116ca63661d6a6dd5006a00ae66a44e8d401b9040a5748490499b8add3210dda0094caf66a94d007ab29961960e47572a94d00500b90d479804d046014631f0c5ad3cdae700c0118cd003801decd695062e287680293cdd1aa5318be00a65294d9b202b4010cee4c1cc0e2eb36b812f4018029aaa
def v4_3 := D 0x60c33030459018134801cabd1a2534013b0e5476b2b91976802199206a0392d5baf2512b066cd123521d5e8ed54529a02f6497b4404c402005a8ca875a7b354a68026a5cc73b54097d340116be5249ce484871ec6b2f6c4074018025a9254e6a94d013d32951dbcaa5340137de62dd1cbb253401421e451a50ec6f72add4cfa054334592a3b6c46967c014a596c9d929a006475b325ece971d5a00866415ba5408452905346b72ed896ac3a053544dc47525d10f65973ba74473b40128b876a00d63561e4ead5528940826eb003801e58ead710a06d00522e803203234b6ea22944a0573348735ab6114a8021edc843441d6ae5d5299a0e044331ae34800cc152da88a540079cc64232e5406b18b0f17472ec8020ad0053350cf04691c2e608dd72046c6902357c402c8cbdd2a5340122ce4a42e5051c128052552c894c046a7b3984050e120541ed2b69c1b4c8205322081290310d107943b5a6c465680459a51b495b253010d4d461ba64066a560d52989ed005319876680f348c1266a11204e5ce16db39d60094b18b0f6b46ca2344a041ab219aa95316e6c94ce8b8029187183b8dd2aa1e84cda00a4622f5830e5621840910c30584614a421741d40ee74b2b82bf68025a42f39a16544c0e6ca2059210809800ac200b739a5b6594193b401480754200e03201dda689529808d4c66106103cb11da96ad29808a642e8058171c2905292774a87430568029a91e24428ee6110532874b6d812d002b32931bcadb25341edca36632db9aa5313ee00a421a20e82b366c1294d0464b9a4c2db9b2534014a1e4021a462ba1310548d48734ab9764a6635c014c6be7310398c987b7439864dc475802903489801c06403ad5bcae20092a0814d528d5e5529a0281e5200e0071a97b54a6802715cc020320032b66e8945a7802125c89a948453226012e5080710c9a21642f476c122270568029a4951da913d29a00a4e76a894d004ccb98f18f0eea556bc28d002332924ad1db202b4010c6cd48c51304608941ce94401c03801dca946db9086ed0052430f3027e018029365b95494a602c59941d40ee434b6c221295041f390e129481807003bd1dcae202b098c0a692b166a94d011eb290a9dd2a02b401c0d1664c6cc3d2dcbaa00d4010cde541d40ef72a887a25b68029aaa
def v4_4 := D 0xa556e6c94d00e9f294ad1a25340456ca45792500668ede55b929808be534868d08032906b6a94d002070c9c820048c100a220a52e9510e69a01b66376b9901c06c039badcabf2d29a02c6546b72a80a1cb68029a90ae76a22950032f2901691101957ab354a686e3814cb51a736827d34010cc83384200c23821ca4ee970d060ad0053480c5100370d707a537954a680294fc98ee555299f6005d7300004880c63861dda56d73975a00a4123a54084129052b6f274d88021b78029aa187183cbdd2250bff5a00a471a70f0af276ce4b405680298ec72b6c94d0050cb916c490025746014cd39dab7512b03c94d08004a80e03201c5a2c95298083be53253b744a6802677cc6c413000009002bc63c3ad5cbae71eb0118c811048c0cc3d59aa02b40081c866a51bacaa534014dae49f966006b1ab0e6b056ed3294d0034398e6125006594edd79299042f656694b2ca34d001a729a49b592a53482c08a64af6694d004177a1992b46894d00f23295290d9b1b7d015a00a6aa39cb2db204cda0094ec64b6dc28d0025729178016019c69c3d1dca6212ada00a69091e6206b18b0ee5356b3294c0489391f809510634887e3a340ec590a998ad225272b6c6b934d02cf029870b72a94c4cb07929092095819835b950d405680f99a941d40eb3674a94d0053b394aa59aa5365e0540a6546543a539daf06d30b014cac32c1d69ced4442698748b6693746894d058b0af948e88cd073806839533300e798049a587352c3a534060cc685d2a0350d507a6b595c4b560c1814ad68d9509580848e433549a7b354a69f3c014a45cae9929a00c87f33252acd529a021265200012002e08c0a104401c63861e8526ddb38058082af3495a3b5c46800e3948a184a40c9dbc2cb62163e0540a64c139db0688be9808a641502560644e6d55650e6988b66a4b9ab5b05ad0266d00524a39b5231a534014c025d180378d787a379b54a68027fdc963561e55ed95005a0046653424a121121090029a6359b6c09a680c794a43641e6e8dd5005a0038e5318f54640c9cd922530105ddda729c8ab22c9924a2d2179563b5c90125021aaa
def v4_5 := D 0xe5e190334b72e6c80ad0043ef911d2dae23143e00a466006806465ae971005808d66891890eb6868129504347e5925679812a00c014a9cdbacca04fda00a604704391d5caa53401211e4eb566a94d053f029a82d729c294c048c393aa59aa540111fc2473143541d6de510f4e56d005227032b13b2880294a3b596c656802199a51cadaa097da00886421a20f473698463a680298464a2222e1100570c7077a593b6c096800b994a63261e45ceada7425005560a6a922244290c82105252f46a94d014532927e39990c20cc14ad3d9aa8a534014c95a344a6879c0148a34a1e256cd4352a054055f343495b54a68987822c968e5d5028ed00479f9930b476d88f9b6802908a09a0448ca01623221ec6965cdd0169a054b66a39d4adb4e0e9a009501900f06572a934c046a3330a905680f348c1265a11204e8de56db3a06ec04a1fdb310ff39487e04641e63261d4ea5edb044240600a6801c00ee736aa94d06db22d92c6ac3855cbaa5340312ca633209a19c34accdba5466a129095a64756a590f3b765542cfaeb401481374200cb5b8a23401115c37f3550a784a00cbb14dab725340ae6c8eae55529a00a25f22fde2b13a48c04724401cc39daaf530e83c94d286d25729a08276332493ba54a68023d1cc6e92210330e30723ab95414bb4020eca42d06500731930f62874a80ad0041bf9a854ca422a21080570c707a493b5c0945bb4014a55ced5287270051b30caa5d5a698377005220d207459b35094a8152091cd09504441382500b12958a516e7356a94d00487f9507503adcba25a896da00a635c19901c06403d993c4b24e23ac014a96e5d529a0083373548f81290358c587378b55e4a6021f5c95c18ac0d63561d69ecd69a0fce05b332614ed4352980b1644cca4229112814b2900488420248a51dae049d7da00a6872556a5174a680290169918195487354a65fb4014c536b954a61802261c968e6dd85c602d0043335269ecd4369913e04332020330032eb276ab294c057331b494a40cc18dacb6406ce5a00a4a1aa0ef6b34b884ac40f029a3f2e9001987183b1dcaaa53477c0866521920e832f74d8228030053263261cdc56951dfed0041bf901018c0193b85954a64102719aaa
def v4_6 := D 0x1d222032b4f66a94d0eab0294ab5b9b2530c010cde521920ee52774d88bf768029a007003cd1bda888a0e9a00a4a2f746c94d00d4329801c00f2774894d00483f91add4bb2512b00e1ca6a4826900b8746014c2d1da8a4d2a00826f27b9a554a68026f3cc52a3754a682fc014843441d6e8d302595a00a6902ae200781980ef66b4a94d0052b391bd5aaa530ec060cc6c85100398d987a357b54a68027a7c9e88c6d96e680ad00535473965b6446db401280174680e042b0482e5cd69529a1cc605303014400ccba2d9b253401435e45a0b5227c5a10f48d404f942025288892394c82288bb1ad5b8ba02b1d8c0968c736aa94d0044b79529dcbb248b40152cc873b656ea6802261c83f00cc1f02540691100780c807597ba549401258029a866822206485e96d906aed0045b201d22103274af2a94d00d7b298e7ae606c49303a05881c5244024bacda706d320844c87534800e83a81da6ce970452a600a68a636ea94d00522392b9da25340130ce639daa2534198c8b64f566a2c80ad0046e39aa8e52cb6dc8133680294ad9a25340448ca45f833206fa147d416c77452d8c04334ab472951014aa840296735b5e0da680bd905409101d86583d28cbdb62cd30116cca32b95414bb4011f4e401c00f06f72a8020a2ff8029a8428a2234a1080500e007593b4090edd3401491e2cc0a702500a5cea6d529a009b3f31d404ac0d23121d6dcd02529a0b96415c2420fa1080588c88795a3b5c590568029a02691081975ba354a68093394a1ee9552836ed01833003801ca0ede5b0351d600a541d40f4a76f2c872b0568029aa3d5aa253401500e47e0254564d221f8e8d03b1642a662b48949cadb1ae4d341f5c0a64a9bda86a5340065e455a2402a9118152a880a8242024cb29bdb706d30e842cd145ced4251a008557218d187639b43c1a53010ccc6d213103a0ea079b3a447b59cb4014a49ecd42529874843f3522874a80d43541dad65310b76c4170291cadd2a53401356e638129481886883cd9d262403da00a4368054064e966d50e875004633429ba354a682c5863ca530476a1a94c046b3263661d6ae59528958087df20001230353caa878ba59b75ce3d256029aaa
def v4_7 := D 0xc8155663c1ab05346d652c94c0421351ac48c019a573b54a68028d1c8620c200cb94daaa5340a9c1cb66930c6af6e94d047af8990101980197385b5e4a6027199265699294c0453219612108308402a46b148ba97583b70911582b4014d404cb1803350a56ec94d3df80163c923521e6e8d129a008f97314caa5d9a5027ed005253caa878ba5b975ceb5256029a51c95ae23011a90c84604a80382100a56ce595298083bf5b32507340b644070d805d60ded4b468817802505e01a02e40c414bc9ad2957d015a00a6a8058c420655ee8d529a028ce528635ab6c42560221992af66a1294d06b329528d9af8a02b4014d00e34810832200a61c60e2b476a221350046329573a54a68023cdcca2958b374a800e3918c84d34a00c030f005ba49dd308a0082c022cd4a963b54a68029c9c94b04a00e03601de695129a008f67300005680e9181ea11203e9e56d738f580950cb74a22944a043d79a00109081794801423421e164ed70269a02be5227813218b2988293ba59540c3b3ec014ca0ea0785b39764fd7580250280160199b756540112fb4014d545a93332d12198295a73b5094a680c195ad1cbb253401450e556af2a95224f68029a51badaa8a5340065e48a06640701b00e6eb72a9294d0163324ae8d529a010765217c0330330af66aa294c3a4e3351d498200ccc139db706d301053e4e70b36c865368028d986172aa8734c058b22380100332b66894d02a04db9a4195a2151d808a486541d40e876b2a8cbfad0053263261d8d6de591743c7004a080c320366840292937ba649401558029aa02691081957ba354a680a0d94923521de4ec95298740829f31e704a00cd1dcaaa5340142ce43ba25015652005a0ea0754a3b5c43afb4014d063861e9d26d710b26d005285b23764a666dc014c80d807a7359b64a68027bfc83406a00d842cc082e49aacd901580a4856a2943daa53228e0a2652b66894d00d67298e20254514f30052b6748229500424b90e1094819b738596c475815029a3f30880197835b54a680153886e541d40f3674895322d005305b14400cca9d22534013c3e46936aa94d02a01979aaa
def v4_8 := D 0x5d82525d8b302ea7941742c40b98a20165e4d6d529a008fe7248c4875b7344a688a9972c9a8ee5717ce0ad005344917b54a68209d859e48c166045913022289411174808f8a201731b30f2f56894d01eb2e99821a20e8b366afc74a6826b94a0e6d5565298548b66a47e91081945a3b5c468015994a83a81d8ee5550e44b6d00531ac6480d60a200a5a50ed529a0960418b9125094818868839d5acae22ecda00a694a366ec94d00529794add1aa53122e00a6358c8c018c70c3ada1a2506ce0082b7208c3a3044bd502105441e63261d64ded70240556096a94772894d0142b2921cadaa534391c0a62e8557505d5bca25340430ca52eb56b88bd768029a0fa09620c2c6105ba300f9a14cd41746eb6a94d00488f94c6cc3dc2b1bb200b400dfca65465439bd2dae04b4012fca41b94320669ae54d9015a0054e433523404c08e36500bc1280626901e474611996208c85100f2e3374a94d005363954bda0a0d29a00a6398e1a9cb00d0e20e5672802b3925941c800a03543541e696d32678f580a541d40f476b2a8ba30568029a4ad1a25340480ca4736a94d004334330092460cb22100a41a40f4ae476c94d004f1b901691100a908814abd59aa5340bdc0a6aa495d1aa5303c91ac9d8ec9529874e2645331ef84400cbb59cab253400a9c3ef221d5290358c58785ba65114a2502a59a422c8801946943bad1da8884d4010f6e47fba544121291fc89403b4690256c353009b9dacaa18df55a00a62c6ac3cb95ad32534013ebe421a20f2cae76dc94c3a51b351ead5129a00a757291ba44a68209dc0cc74812c03334b69c94c085b295c65c3b9955ab7251280c7ca69374e6a94d023f0af948667a8c17034619cb481cc0a40495a73b54a680c1597254e6c94c26307929286283c35d2aa512890c08866a8b4824406660ed552a119e0453202d323218411829578b354a705b4014c77812a0328d28753ba4114a802275ca8ed65717860ad0053472951003a0da076735b5e0da680dd901719a01c06c03d18daaaca186da00a651dacae5340112de41880580656ade550f47e6d00535003801e8e6d305074d00524d50310300e007a39b44d41cbb4014c6f8128032752a894d004ff390ce01986600c814d11adcb2e4d2a008c6692556e6c94d011b72916109481886883cd9d2621beda00a60ab9daa534010e6e509b4e4098d1f06b2f6d880229b025aaa
def v4_9 := D 0xb1ab0f50ae76c94d004eb791bdcaaa53401462e502af66c1294c3a4e33488591826b08402c06c03d491daa534cfc0a26494066449cc320526af72a92813f68029801c00f4e972a94d004fe3922cd9aa5340a85ecd4908f682ca0b40b905201e3971c8991c3d0c6a5d6e27503df004a40c130238d9411c9c801ccb95d2a5340137ce624d9d2a5340141de44e065625812a0532e56b4d88d0041279a50cbda88a5400f2ca421a20e0772aa94d004c8b98cfba400661c60e54b6ca94c183022d90520160197ab59543d397b4014d5249e8d529a02896524359b54a680273dcc40d4077ba544a6802875c8a34a1e256cd4351a054055734829a7364a69838114ca94d9e591a06147680298329476d88d0f930294c64c3ad1dcaa6a02c0118cd4b0cb07a37b5964457b401282c18801634100b01900ed2a76a93d4c046b309705841502a00b11910ea34736ef872d045aa1f81210398c98769b3a5c114173c014d1c084841942100a21ad442e48ead70244eed005201df3403347368c434a680298cc3a54066cde561b1100eeb0052048034032c52b56c9284ac04433550a544a00cbc2dd288a072da00a4b18b0ee70b6ad294c0414f90fe09581c06403c9bd5af202d3014cd05ead57a9a00f56520b5d1a07e48c826348009163012b1ab0f2e716ac94d0d1f029831c30f2c476a5ab4a6217814ca165ead928958085e735255ecd529a0277e52478b30032352f6a94d004db398eb825475e5290534b0f2b82bf616802911869008b446014acbd1db088682d4018cd20214400ca34a1ee5ce95929a00a4f7292ab7364a68062f94c617b596412faeb4014968a1d529a003ce4335400e00793ab4c28bd34014803801e5c6e9529a008fc731e17460f092200a651ced7929808317210c12115f09002c46443c39cadb604d34156cd07c54200cbad1da86a53400cae4b1ab0ed56f2a827b91680298e6cb6bc28d0081b29068d988197359b5c5c3a00c014d48bd13045c89422c94401c03801d485eadb9086ed019b2185511032526c894c0d6323598e0c2620621a20e62eb2a8147396802954d9a2540115bcc6694e76abc94d1db02940abdcb06a00d4009ce632708801cc6cc3ba9d22534013bde4af746a94d00427f9aaa
def v4_10 := D 0x111b10ef374880b4d0016f93c80160193b59443912fb40148189cc00c8cbdd2e234017ccd1e8c56db9067ed005248d4878375b5514a68010dcc00e0076a3b95c4267b4014843441e2d65cd929874549c66a4b1add30c1d0396d0052a0ea07ab35954056efb4014ca0ea077b95443d3f5b40148954c440cdc9d2aa530e80a8ca686a9531516874b6a221350052329529dbaa512b4060cc1ab695ca60c1810cc81924200e3028b2644813a739554b50561d029aa646643d2cbdaa5340150fe421a20f3566894d004e5f992862cb6e90cfa6804591700d4019a258c445b1abdcb200c0104dd68e84a520621a20e74b69892f76802915a09a807042014ad89b2a530116d2cca629554211d40118c81904840ca2200f0108078c1271644809272b4e6a8020a4a3a05352965ceda9a00b65485904206649e8d529a01ae6531cf24a0e74a400a01c00ef36a9c94c8219b27ab544a680219bcd1fc1ccc0d23521d5e8ed643694d0052378f2c1ba096004348c47ba6423e13100889006a56552ac5d1c5acb2530ada00a63e851f5058c2da6723103c0a4b18b0ef24d6ab63177a00c014d544a3b95405a6801f3c96a4ccc0cbac21db052d29a030645f0052066616dcd82529a06fe53428d2875317b5e4133b0116c9c8d6d6652a0063e531135cc8dc4e626dd031220598048c0587005cb95d29f6d355a00a42c00620601c00e92774a9a80ad008b35084144468c2100a528c6d42506aed005210d107395b4c46cdb4014c74c12b03274b6988d0085f29114e91024746843ce42041b1909346b36ed9c02c3a053432ab7964a68092f948080c600cdac39aa533e8138cc6b2508032876a2a828b680213fca8ed6573c415a00a6a8f74a894d0053fb91c69c3c9dd2253401386e62c6ac3bb1c5ab25340427ca4530058294c331480118a330c83b16601656c05cd39daa4888680c014d1e168ed8452a00826f23c0510032e2b74a94ccaf020abcc3a29b5d14a602359510d9aadfd015a00a6a44e8900197859b50d4a680cd90cda22534104ec66611409181c06403b0d425cbc671eb0b01484aadd51a00972ff334a98b7364a6811f863ca4040660065d68ed4269a00a8662dc39aa534013b7e4b99459316c6b36ec8030043af5aaa
def v4_11 := D 0x16790019a528b764a763b40054e401c00f6b526ec94d06cb22d921cdaa84a5340a8c6e6912966006b1ab0f4b056ed3294d019b24a672a25009512d0c8895824449a611198a8892f2840983a20226cc9a5529809de46b3063861e608ed724369808a6521920eb2f6816b205a00c014d4b5a39764a68029edc95604a8021a442f053107824854b0529129379b3a54a686fd814c7701320326d2b6a94c863020d7c89884c40c9dbacaa32851da00a680a9a400731930f02af6a9a950052329146143b9cdaaa53408fcab66187183b2dbcaa7eaeb401482404a80ccabd9d3625492c014d52965ced92a00a8c6a4ccdab192ed504f14441e4a49d5a764a84973195ba6410792c012c9853b5883a534014803801da4ee9710ed6d00534840d280338d387973b4114a8016994aa561cd929a16d005318e96d711a00e8e5218e187a5b975ce01258029a91cc25006568add529914701db2493b854a8021a39e8e63a83919d52cc03f22300f01900f12b699c1a7ac052a0ea07849b3a6c4a9680459a4955b9b25340491ca47752aa94cfb008b319f74800cc38c1cda6d552983060480b902209500d244014d5ab4aa51281081c866aa5429bdb08a534060ca63661ede695529a00a2772008718032cb6e6a134cfb05433459812341518c21718410ca8201391990f526cb6c94d004897921e79801a46a43bac259b28a5401048e6012e8c01bc6bc3d31bcdb2534013efe501900e8434f72e9202d004333523e98440ec32c1e04dd6d84426a0065e5273895b64a66dfc146cc7081323af09882932a59540c3b20c014883481d166cd4269a054b6668c764894c046a53258d5874ab7954a9fd6802984f72aa94d003a371903e011819044416092912024793cad2a00b292c014d500b48840cabdd1aa5340504ca4b1ab0eae574a94ce33802992a76894d0050af91643980199653b76e4a61d2899a1cbb2db04a04cda00a45356e6c94d00cd329941d40ee54b6b9cd00233293955aaf251280a8ca6a4608901d054401403801de56d38369a033649f26664ec033052b4d66aa294c058b31c41cac3a82340a681de296d70478f580a409be681c4034052ed36aab28bad0053424412303404aa208b3a97b54a680243bca83a81d6e5d12d7f5a00a6446c43dba9d2a534013c1e52b446ec94c4ff8029aaa
def v4_12 := D 0x406400665c8e9528b37005f3248c487593744a8b1c0172c8ca2cc03c425032612019108c049649b55094a6815859a520dbaa534104ec3bf2253b9764a6699c014ca7b544a802269a10e42b4e600668d6e55251a00be66a1cd922531efc08a64818260471b2806009411c9c80189a4054d7102a428807d07503b8cdd2a53401373e63955aaa5090e0083e7224a510121284029841395b7c0968152219a012288019375b44a6802953c95ecd29a0088ff43309ee55529a00746532094110032736b4b802ab0043335472a9b564a6a1bc076ca55ced529a009ca73194ee5d9283c70041d792c62c3dad1ba88d40106ac8cf34935ba5c975b4010cc98cad0f1e94c046b31ab04840c8d39a2530108eee641c943206656e9cd9015a03d4866a187183d2cb9db25401048d4a020620601c00f473689a8597680298e40a520691a90ef6b482294ab00db21c052000028c04d14401ca310945ab39da8884d0ec118cd2561cd529a0241e52953b44a680260dcc18e18753b7954795c8b401480d3cc00632500a68ed255b92894031e535525ced95004266d005273b244a60243594c963561cead5d5289600386534a15b7964a6802995c862044485365009c12807b0cb07739ab54a68020b7cc38b5954a801539048e42b00680731930f277489a80ad00535314298a82d469cd529a00a76f200e007927ba54012cbb4014c75012a0348c48753ba4114a802e59586583d2cb9db604d30e916cd258cad45c694c04353952cb1db2530162ac6865290310d1073ab515215a32b401481774a80d4358a85bcdad2e212900e00a6a8b582220a01280588d88772a9b54a6802469c95704ac009a4600511807820824b0509111353b7954a6709c014c02002c032f36a887a25f6802951abda88a5402f2ca683b02220761960f02e76bc1b4c045b229b3a5141d340140cc932b4117a530114ca6294dd8256944a0414f9a913235006e410205ae90920c02ee2b74a8437680cd50b009493544a01663661e9e6d129a03d648b311c6ca00cbc95d2a53401400e4342e400656ade5500451f00463340341290308e08737b9254a62ad8114c8d4348c0c43441ece9e543698377005328eca5501698084272995644934a2d2139536b5c940125025aaa
def v4_13 := D 0x5d14400cca9d22534013aee521920f4b2f6b822834b8029007003cb1add362072da00a6904861088d5080532c476a94c046b1324be73425c01a02939ab555940bdb4014c82ca4058b6392b5c9a602295507503cbdad2a00896da00a6a187183c9bb2db70ece9a00a527748950047c38198c34af2c94d010832912e09a019873b956465a6822d9a07209180b842014d9ab223401221c867235b7950da68030b94c00e0071ab57964145c8b4014a03201e8d66d52790f580a6a94894f518a51e6f2b74c88e368025086883c4ad9a86a5340123e60b1dd2c3ed0a06d00522e9b31172890029a32b75694a61d0859a41ed1020e00801683a81d6adcd529a00a62f250d5079571a3641619cb4014c48d487a53b9547cfd40118c83e74a81082320f411107110ee5374ad812024b0053511c6ca0181a400a6165ee9929a00a717292b6354a606c191acc72c16a1340ad02de052e405b39cadb7649eb01288124a00c43441dce6d579298745b65347f85100398d987a9537b64a680291dc89c04d45b826401c108072b66c894c0432127992e7496c94d042723e3c963161c56ae59928945fe044335500800b0b840440a65d691004846d005209c1280b428802c46c43cb8d5aa5340144de460104206615ecd529876056653458c91142a79802a46a43ba94dd34ca094da00a403a666430833052b4f66ad274a680298e76a894d03ab22d908e89801ac62c3dcb9d2a0082890e00a6a1560a401e6938b9666a132238bad4b9db60487be00952ae76b4d005b31b315adcd52989cf005200e0071a3b95c405680b19a486c83c49539b25344a0c0a40f923207e52805232b6894d0c630298f18f0eb2c6f6dc388eb00520681ac03a0d581c8aa80d83540685a90320ac06aa714a482a2644497ab5937640139251d25aa4c15b1b25301dfc8d6421a20ed4772a80ae2768029854736a4e34a6802916109081886883c9ad5ae0485eda00a6930c2af6e94d047bb8994ad9a253401330e65249459ba5155e008c6419ca5006c1cc0e34b366c1280ad02a4335260ca9edd29913e045324f973327aa1993c4cc01cd1b14a8c3d29808d6638609601995ab4094a684299481800d00dc31c1e8d65173e80ad0053430e30735b944a6802439caea55cd92a581ed005319400b00ccdbad2a009c2da00a4a96e6a94d00424b9aaa
def v4_14 := D 0x13b094847842014cb15d1b0482c8b4014966cdd529a00a2f72563b754a61d828fa2cd2152902a2ea54ed527a9808a641a825401c108052b072ca94c04e24331ead5129a009087200e007739b554a61d815175cd48e812a0350d507793ba5c445f904e00a4aac2200731b30f46b2894d00454f98020256764d233b109883a4502a54a260949bcd9d2a53419e00a4001a5006d1ad0f28f674c229535008b3415a7354a680295bc8af84a40c43441de4ae97118fed00531b124400ca34a1e55ced5ea61b4d005209db28032a8f270c8035005cb35457b344a682a581485d6e9529a009cd730668ed529a008d5f2c8cc87a36b95c40180209bcd023821c1cec9529a5fe0453239b244a60235199930b66ec94d004f8b903809081995a7b36405a61d88d9a86702220661ce56d83b74d0045b2510f280300941463c80a2b240518b1828ae8c1442c400c0a20226dce95529a00842f31d33ea0e91f40745998075a4a2c48b738a95b7110da800eba87800b03b80461d8b300ea68c04d06d038d3cdae088680c014d056dcd529a00a457280c8079b7344a67d02093cc42d7280336f34aa94d0042b792c62c3c4b2dd304ad289408866aa2cca84019672b354a61d2298993e20901f15460f802100e4d26d12980ae453f21fdb310398c987a51973b79d1109018029a39028c8a31444152356a45bd2da0884d34036c943541ea2dd26529803ce2379831c30f2c476a1a94c2bb229932cd9aa5340a90e6e6a2c9bdaa53401059e4e5572ac94d004da798b366ea94d004197911609501a86a839cbdd2e20086ce00a68c1cc0f6f34aa94d00526f942bd9aa5340315ca651dacae53060c0873f225ab654fd25602219aa542bda88a53400b1e4e6b6812fa68023efcc3517b5353a53401488a84840cd121dacbe0489eda00a68a9276a12950042af90c68c3b1cda232ce98086663d5aa2534013dbe531930e92774ab8340568029a9476b2b94c417021991cdaa2534010ccc7021290310d1079b3a4c4809b401486e3da03502d00b31930f06b36ec803001c325a01691081975ba354a6808e5948d74c406b0a200a64d69129a00832731ed4e9529a009dd7200c034004016029ab794c4a968029aaa
def v4_15 := D 0xb66e894d00421394c311db21bd29808d64670262334129052e4d36ac94d02a16f2d9a3c269001983a5b5114a80231926801a0092cc014b9c15aaca530114cc30e30792ba354a680425949b22ad242dcee694444560ad005350738ca00c995b4aa0d3e98084d7210d107a713b264a61d02339cc75943b60a5a3401058e4503a5406d1ad0f29674b857f0568029a02c6900191579b5114a8096d94a23221dcee55529a0b1655b306505680e30291202da9ce56df045e7ac04a80c807a73b926439a61d2299aa495d1aa534051bca4b29a66591d3213608c8531444254326a85a10d5ab04a083c9600a64ac59aa5443da00a54b366a1294d02a32b9a16109088384201443441e4a8ed7024ed6d00523a5879641c1b0b4014c90c907a57b44d46800e19485006a426135012892809e49004e64602e092880b8e414a54500dcbdd12a530e8ac2ad473a9554a68029cdc8d604a00cd1cda253401364e6406403c955aaf21eb0095ca441c2400668e6d570269a057766811c10e26f64a94d24b022991c89998192a9740a1d306ee00a6340090019871839bcdaaa2eb40116ca92dcd52987483f65b35500924600ccc3a9db2534010bce404825006f1af0eb52e894d0043f7918ee950c684a414d1dacae0afc15a00a689a2666066a1d16d829694d00db246473423001a0295a7b3551a6802d9987364894c2bb022990c001a05f8ccc2f28660e54aa2dda65006a01b66a446443ad4b9db620d6e0094b3436a94d047bb8d9861c60f4ecb6bc23b3a6802911e01608a94a41523521cead65711756d0053480c807923b4494602292190ab9daa5340131de6362e9501a86a83d5bca621eb060c0a40f0a52068d080598c9876293ba64d405558029aa395d2aa53131e002a728ccac598b91573b64a680271dcc7653b54a680285dc87844a02642100a21a20f4e76822740568029a007003cb9d5a88e8d340148be04c80202523d8f211eac908f474642e052b04a2e5ed69529a00f165306804440e03601dcee4a9929a00903f204011a06488c02ac6c858b97a3b5110d05680219a8f8b230065d6ad129a090d7132a97b354a6806b594c71a12903270b72b8902b680291d5bcae1d3c15a00a6941d40e4d2b6b9c8c87b029286a8392d5b2a512b010cee6246243cc2b9db08a54127c0a53566894d052b029aaa
def v4_16 := D 0x12b46894d00e972902658c01995823764a68a7c0149a35a1d968ee5b101597c6053459cd08032e72b6a94d0056f0b3c91504cc88023444c119073530a76c94c38b02719981980f52b166c94d0fc30290c4184019739b554a681522d9a89982d02d0148058e5c76044c8e2692b46f6f881ef80252a2094019b5a9754a2b3c0118cc6ac120356a8c029b147354a602b90c5c8912cc00cd21cdab04a5340a886e68b2f56a94d005293901019801975ab3551a6802a198d5a6660661c60ee52d4adc28bad005248d487a5b97364a6168152d9aa51adbcb25340509ca4af8c44578822052b4f66a94d0e43029853566a94c30043f790868839d2dcae22f4da00a6934ae76c4af4a68029086883b1dcaaa5340133ae634009401946943d09adaa514de008c646f36aa94d02a06f39a8f734aa94d00535f92cbd9aa5340150ca638e5900b0848014a49559b6049cb416ec89a6ce9b014ea6d00534531b754a68028ffc995ecd529a0070e53166cdd529a009e2f2a0ea07ab537964051ffb4014d5418e1875b7944a3bc8b401496900880cc1bd92a530e9c3c8a66286a83b1cdaaa53401446e408c442064ae69cd901698740a66801c00f2e756a22453a680291fa09510534887eba340ec590a998ad225272b66ea943938167814c88d88793a5b54a7d5c0118c85530cc2a186414042807300f46f36a92228030053519454200cac9ba2534014e9e4a1aa0e0b56ea944ac01e711bcc74412c0332b746a1294d03bb29606603954dba88a00c0071ca6900a442800821052b4f66a94d0125329010198019739a552c3a53015ccca0ea0773b965645d25dc012896ad9504b64ac0443354a837b264a60211d94c8e34e1c9a8ee591c0e0ad005315ced129a00835f22865290310d1077a3b95c40565df814d28d6e5711116d00525a37b5c468651814c95ba354a6807af94ae5ce95004e45ff005352a15ed44529a006872972ab522da534014c531b75a68027f796c856ade5b12a6008c6686b36ea94d0051b391a50940d1848016c32c1de6d502529a0542df319008ac0c9cd5aaa533b3e0116539156459324945a42f2ac76a8024a2bb21aaa
def v4_17 := D 0x3bc545fd2222fd2110399a7344a6875981482814400ccba2d9b253401461e4c8b366c1294d02b7b34881f3443e21a1384ccc1d63561dead516529a01b649306640731b30eea774a9a9500417f992e374a828fa680b1900009181a86a83d2cbdae70092b014d48459b36094a680af9495194200c03801c6ce910516d005033143541d4ee5d529a00a0e7210d107829b7360d4a67d0299a486c83cc1539b2534afe00a5492e76c94d004c8799276b4b94d00439f905001601976a359645bb82b4014d5003801da8ee550ad722d00525892232c321182957ab354a673bc014ca5973b64a6802873c8aa14a4291a100b91990f2e374b880a5838029a42d9baa534014c0e47e1a603ecd281f4c8c0f96440269129ea314a3c4dd615299ff0047979837026a066946e5da9905f004332108f300380c8075a7b9549401802319a941d40f2b56e6c937b68025406403d4b9daa4f53010ccc75132b05539082c46443b9b4adb62cf1eb01487604a83ec6600a4dd6e543529a054b66921920f4832f6d822840380291820988e304a0711640385920008e8c05c22560c45d5a9baa534011dde633009501a86a83a49dd2e2200c36700520443310200948299635ba6114052502219aa8b7a668292528052eb7489a856368029406403c391b2dbb4a53011ac82304880e83a81d68d26db025a00837f347309100300e0079735b5e22dd34014a63661d0d6e5529a05403273163161d8ea4ad929885e052a80c80763a79b6494a680ad9a911910f4a36ebc94c043ef92a0a84019537b40d4a68031dcc759d08032a76e894d0103b459412d5bb7512b0069ca6901900f2c556a86f4a6022994955b9b253400e3ca62c62c3b9cdb2b22e890e00946556f2c94d003df29aa007003cb51dae2501da00a4e72b6a94d0047df9872b683b34a6802915c01608a9484124a100e5ca6e8db026a5a00a6801c00ed4736b8859768029507503a3dad2a0b9ff5a00a60c70c395d2a721eb008cca419825406f1ac1e2e966dd45c68024b0053522d54a1164a400a01c00ea36e9c94d3470cd90bc08886054401623621dd96cd504ced0057b30a34a1d96cdd7a99040a86474af6a9a8d0074729a3f289401987183c2db9aa534475c10e7280c807362b95494a602359809a4420656adcd529a01de652573b44a6802a19aaa
def v4_18 := D 0x163561deacd6590144bed005209c510032f2a76a94d00516f90ef29401d07503bd2da62158da00a68e76a894d00453248d0310300e007793ba54d4143b4014c32ab954a680423d8c803801da5ced5929876056f66a48011501939a5b54a689e5822c968e5d529a009bb73146dcd529a00a0b72250034032d4772abbb40568029a40a010019a5397b64a6802955ca55ecd52985408837324a2dcd929d603d4a413006406a5080580c807b957a364943d61d029aa1952bcb2534050eca42eb56ae5b4a68029930b476d8855768029507503c9bdd2b6340105de9668f4772b892f3680290ad9baa534033dca635a094019b5a3454a2d3c0118c83b0cc00e03201e48ed1251808d4866a056582ac5bcd2daa534016fd49cb2100664529129a0827619398d8ba5406a1aa0eb6f29887ac417029026b04074242014c931a25301073cd66832eb74d89217680291b92940dc246014dab39aa53401309e60000cd01e691824cd4224098bcd2db673103c0944c8f36c222ef4018029aa80400585b20220532f74880234f6802901019801972583b6694a602719158494019985b376e4a601bf94d0569cd529a00a66729a357b64d46800e394c3fdd2a36d0948fe44a01da34812b61a9804dced6551f67aad005213412a0378c787975ba5c401258029a801c00f2d476b8856b680292c62c3ad93a25340079cc4f31d104a80cd1dbcae23400eeca444824408492104328803d242024d3d9a6702b0e814d0da0ad4dd694c046b20203300332b4e6a143a6802a198d1826406409524116c7256a94c26302a190265804c5c9dd226a09dda00a6a82d8a200711b10f3674894d0053f792b039981a44552885ad39dab85d29a00a600e3998195a73b584da5340149e8ed6591a00848e4679a0f028887884201403801c5e8ed426569a00a436ea74c94c04cab0abcc3ab7953a7d3403c94a63261ce91656751a00837f350b284200c03801de8e6d43b694d0052a9b744a680f590ccc6f41313720949ba04841c8d9cb2a530174866e43592100664adcd529874839e533402c6210334b6e6a94d011c3291aa0958d5348c14badd1a84d306ee00a605b2940282460c94e2064451009850ac2a0b59372ba74a680276dc9a31a1d8e16d460e12f4018029aaa
def v4_19 := D 0x6d7a8c2c83461a5b510b80a898b2da0c502d0624f603100b003a3d60c382b00e0b5030c0a81852d20c202903a5e96d129a002a6a29ba350d4a608cd94ca85ee57100580700534826334448e1a0293965b5594099b40148cb44a093ba404b0b18254e8c12e14402e63661eae5d129a03d6421798dea4420661c60e507572c20ba68042594983981d965ed7081680300535283a81e966dcd927aed004a22dd2a03306eb74d884aeb0053168e5d507fed004432150a8aa0b3ab597640a3b4012d10a68edb11a25a60527629b564a6803bfd6cc08e0878379b264a61318114ca6d5e8d91969874824f354a98b354a68a2f81493276a8640b5213a50807828a44b15e41525086ce5ee8990fdec3a04b1ef74800cc38c1d8e6d5529a20604332a3179569d40bdb4014d146dcd529a00a637240c5302040941017460800a201312958a516e6b6894d00479798c1cc0ef4b6988d001c329096e5604b01b0250058124fa3090e518496ea824015411676107ceb08439d44123aa2114b6807c0b40432d601202b03f251489064a89d2cbdae70092812d4100a8a00b79a5b54a680ed5294b11949508c149b592253361c08d66507503c39b4adb8886a540075e44102422065080510d107953ab5c0905680459a406403cb11dac90d298086a72a5973b64a60220daca3cb5078b56397b6ce475802940bdcae200ad9e00a6aa2e2488019359b4e4a6020abca54ed129a00877f2315d2218b090829a5b795ca915fb4014d2183cc00d23521d5eacd5452a00855f243973421a01a0293a9b555940e9b4014c2345100332b66ea94d004fbb929bd5aa512b010e6e6a47ab0c819972a5b6ce68012b94aa55ced91b774d051b3096dcd69a00a07f432104a8a08b1a3b95c10582b4014d24ee9552516d00443294ba354a6802637cc6c15080300e007719b554a6817d9203e40f025406a53005100e9076b2d887ac3a2a535460011104e09402c46c43b9acdaa53401235e54f2b6ae2f4a680298f302605041283cac901e47460f1a6207885100d2c72a894d0050ab913509084b84201723321e5cead7044e0ad00534a1b9754a6802973ca03201ca9965599e94c046b3183981dd4aad711a004665280c8074295b3649468150219a8e7922029e1080500e0077395b5e0edd3401493d7cd09d306839533326f2198497ab54594a680c19861c60f1496822950501f0f9c9a35a1d968ee5b101583060534351b754a688f7916caa50ed5929a0182e8b31557c800e03201d4ea59528958087f72a0ea075b79443d9168029aaa
def v4_20 := D 0x7953b54a6802751ca54ed129a00a2bf2a9385b6c46805f794d16e04680ccc1daaa5067e008a6440d66a94aac046b324ee912a008f8683f90c339886040c414c9add2a6a072da00a6a29dba253401146e485ae50066de695529a009b97325ee8d4369a00d5652739ba5609a61d811194d204188c0e63661d5ee8d529a5470052657b354a6824b814ca3b595c5d6802199048e8d01c46443bcdd2ae700aac014d524a2dcd92a86701ea5201012a2c06910017468498a62130590a960ad22526f3674a94d0e4f02982b572ec94c30042b7916eb9581d07503a0d5bcb654b4010ccd1c5848440c2100a21ad442e8ecf02472ed005280c807362b43c7a53010ccc38d387823b7964a61800e19496ae5cd929a0548def35323321d65ced529a00a6df218e187a749b54d42c9b4014c10d10785b940d4a64107193cad1aa5340a8c0ca6811c10eb6748828f369b4014a03201e6dcd106ef4c0412798cb86100669486dd929a009e4f228c287439b55094a2580c794d5473b244a67418114ca9cad1a529806465322f4034032f4772a16b40568029a42419881996ab4494a609939ac9098ca800ba340a65cd69529a1a3605324ed512a00878e1239080545005c3c959b2530e8a914cd472b344a6021d394c863861e45ee95004b26d005302c04a81102220b41d40e42e76a221b5005cb26439b8640180229d859e6801c00e4356f2c922277680291d49880e91440030e100e694e5d529a0098a731a400d0d18c5868802c0738d3879b384c4a975802902c1980150ca01663261e8565ad937109408866a931b30ee534aa94d0053eb9086883d1dca383d015a00a63ba0951dd3488ee0234770d11092a06e4a134d04ef20d7c8a200a40cacdd1a84a534117ca690ae76a22950031f29007003c9dd2268a0e9a00a60bd5aa902e9a008b641602560691890eeb566aa294d05cb350c38c1e58d6adb10266d0052953b44a6806a7a2ccba92447ffd30114ca23621e8dc6d5929a0540cff345973ba6c1a5b4010cc8092c600cd9439aa533e8114cca52b754a256800a9ca139352409921a4e0dd66d860e12f018025aaa
def v4_21 := D 0x6ef0c819ab5973640568020cdca52ce9529a00a3272332731196818829935ba54d40bdb4014d2224ccd1028660a60d8ad54529808d6496a6684b0034052b4f66aa28d0041639865572a94d00f3632926b354a61502359a85d024690951105336f4894d08c72b99007003cb95d2a6ab40140cca9587364a83fb401489604b00cdbd1aa84a5341049e68b1ab0e52774a94d0052c7932db9ab24e9a0086661dbacaa0c5da002e6520b07ab0560ad02a2ea00f3b101301900f2f4a76c93c7ac04b545555080332a76894d00545794ab9daa5340146cc88c88783795b6c487bc0129e4ed69b005a008666941d40f30b6e6c94d00531391f84980ff74807f3a303f491009a4cb5198b29a375420fd30174cc5372ab6c468040d948460cc82182520a65cee971015a02b66a216b94019739a554a68029c3c963161cde16d6652980829f306ca1e1cca83c5a56d78738f580a44006641fc12a05326eb74d880ad0053347f4f200ac288029953a44a680291bc923521ed6a4d99289580824f319e5cc8ce98640a59d6e55e768bad005214ab354056802377cd545bc9080336eb346c94d04e8789900e3108193a57954a68089994a296dd44528940829f348503320388d8874a39b54d4a80209bc8d02c6202e8d96e5925175a00a6414da06a5310bc0a6491890f72e74a8020a4bb8029a8550290079a466e599a84498e2eb52e76d81235f60250c70c3a4a9dae4d340146cc020330032eb476ad34d00543238ca9e18b97ba4c4012bbc014d143141dd4aad6652a005465248d48761ba254a0dbb0152cc70c70758173b69dc47580295294dbb2096da008866a8c26b74c42b4199b4014a55ced69a1c4605b332614ed529a0089ef212412103a0ea07a2179b6110da802f99a012a8401d07503b2d9baa534014b8e4b18b0f2b06ea49b4a6020a7cc975ba364a618079319086883b1cdaaa5340a9146e6a45e8900197a25b59a5a534066c93b8cd09d08684e1333272798049b78a552c3a534036cc6d0730362c981b46ca0d88a500005180b26974aa22134ab0418b9007003bdc9d2e200ae6e00a68b2f476d1e34a680292dbd1aa32b02da00a62c6ac39559bcb202908da00a4b2546a94c5278029aaa
def v4_22 := D 0x8809602724601603601d4dead529a008fef27e13100334e372ac94d0051779346b43c2bc9db08ad015a00a68818260878f2843a0941fd3c810e3240515d18436588056144044bc95225340142c8e6e955299a8e04433043441d166cd42529a09ae5268d687837b95401052b3c014d42e0123170e8d028c70c39a4bda8a4d29a00a4aa02500701b00eb52e894d004deb98ec00580652ade57120c6d0052208a220ea09102d07503acdba6725ab014d037048c05ba100a589d4551a00910643394ab59aa530a8162cc739b554a6802407c9924cad8352987403ef35448d48779a5b54a68046fa943541ea15ced929a009ccf31ec5cc0f5a6207a85100734ec6b2c94d0050db915009501a86a838cbdd2e200904e00a682b6e6a94d0052fb939d2a20c5da00a9660d60961b558201603601dd4da6d929a00904f21010310368880295973ba64d405258029a8a636ea8d0053772d923c59811c6ca08e4e4050d710284288059973ab54a68026bfccb0cb0712a7b561109a55822d90860839954bdb0486a53456cd24ae8d529a0244e52865b7364a680261bcc20c2079623b579ba530114c94da6ad8352895840866aa2dc01996d1cc014c13d9aa8a530e914c9f14ccc0cc38c1dca5aadb850266d005280c80793a2b50d4a6029a59a388d0401998573b6e0da6027191469439b8daaaca099d808b664165202c5b1c95aa530aec8a542b805816502905347728873f0568029a971970f4e36abc94c0419b9295b9aa53368e00a641a520b45b5aca621eb011ac88838880cca5ad1b04d340a940cd14edd129a00a4d7290ba35465a602c598d082440631c30eed2b6a16be5d6802900009001774601463988c5c3d2dae712b0110cd523b04b00ee32e1cde2d5792980856f24557322b4d989152cc01c6901e1a9803e5cae94fb72b4d00530080cc00cb9cadaf253015ccaa32a1e10e56db83698540a6683d0a224cd13019308403806a600b34a59b6094193b401496799c587263e1650ed92a0f0e04b1b424400ca994bdb75319ee00a419225006b192162d1e4ee98450148070053522804880d43541e5d96d42d7c133680292cc59aa534357c0a638088c01ac62c3a54d9bb0886d30c010c86e0cc00c9d5acae00c010c98cd003801e8ede55050f22d00521585100332a74894d0057b31742aba82de54e9529a009dcf20040340010948293ab595c46568029aaa
def v4_23 := D 0xa3ca00c995b4aa0fce9808427273b544a68028d3c8b286a00d2201d4a2803dea6d5529a0542deb4a437b964a6809a194850044499a2404c91180748d487875b4514a6808598dea4420661c60e507572c20ba6807929429bdd31cdc05a008666a480555a3f06ac14d1b5c932530109ad44612500669cee55b9298c8e0531dd04c80c9b2cdaa04fda00835f227d12803214a1128b692b754a67d1d0859a0ab9da88a5404b5ca50ea76a94d004c9f992839a05b220386c02f2b06f6d888178025429d3db2512b0150cd52462c41228a200b91990f2e756a94d00546b92c6298852942014a316945bd14d9b06a1fbd8740a631cdaaa53401442e431c30eb4f72b8802bdb8029a007003b51dcae24c7da00a4830a604145282090901041460269391ea33643ee5e8951a1f4d05d3310c00600e43641d4eadd5299f4f00521341180318c7c316e336b4d8024b004333510edd129a0a72e5b201de2929a91094c20841ccbd1a25340363ca639a0b489b0544167641c996103d1668ed825041eab04a20c12a0334af72b88027578029a3ca9dd36100da00866529746a8cb4c0441b994896a1116b2f670d8eb00432a50d5075ab8654a25600f390cd545163b5094a602c592d1cbaa53401451e541d40ec756b2d8824f68029a434598019952a376694a680bd922ab991176cc48b2062454b3009180b0e00b972ba54d95a68029801c00e2e76aa94c29b022d90b0d5585406ac1b4eb20801590800a885ac62c3badc2200d4036ad42c451116308402917a3b5185cad34014a55ced51a0082c71b324e16d712086d005222812203c49802c064038d24dbb6700b20814d060ad311808a486403bc563b52231d9211839b5a7354a6639c014c928b7364a75801c79481c04840cb1c3adb21ed30e946cd5254adcd929a83f0052a76b9564a6871b814c01de2b3d23119e8908c1c92d1baa5342de00a40c36600649e6e94452a00be669346f6a1a94d0031b9529dcbb253401337e633e09401935a9754a2cdc0118ca4a2cd43501580a4866a521db4b6534014d4e4c59662b16e74b6a94d0034358e2c2520621a20e6b729890276802951adcae1d2c15a00a68490334079a4609335089026d46f2b6f9cc87b0250c80888d974a06c3a400e51a50f62f46a94c3a04553986b1a400691a90eaf46894d004f13901018c019763b554a61d02b99aaa
def v4_24 := D 0xbe02605ec1282f46901797c40bc42205dd1080d328e74a94d004e9b93ecb941f504a0ca324052c5103e8a8405a46a439a4d2aa53401455e44d3674d8beb0568029a2db29400944201703301cd6e5129a026765246433222e0991145ca8890254450211224a8890e38409012202268e6d12980bde46b3003801d868ee5b1099ed016321551a80300e00773ab95640e5b4012d425a3b5c468012b94a4ee9551b86d0044330e34e1e8e6d309c74d005259a3b5094a682243cd056cdd529a00a537230b295465a6023598d82a100601c00ee736aa94d02fb22d9549bdae04a00aac14d5165ecd529a0e3605224012a0330e56b4d884a34b802994e372ac94d0050c7900109084d842015c31c1e4a8ed702415a00a683f8242070a9481516d2b699d4c04532a51b35315a02b4014c7632b54a6027c194c83800ac0ca94a59b21cbda008866a3dd2a2534014d9e49fbe684314340527436aab2833f680298e5aa50736520052c736eab294c8210b2957ba3609a68150d394d1fb3c200c955cbaa53401481e493566a94d00507298e736aa94d004f1f901929401c04520885d28bd9b7202b156c0a6aa507503b9d58ab251eda0094b50068024b30052e7056a1434a602299804ca500668e6d129a0087cf22ed3080326d6b2a94d02a1f334957b3a64a602449a90314cc843e5641412b002691907746883c2320051180f26f6b2a94cd1780298e736aa81d368022d9090095019b793a5c40139dc014d43ce5280380d80725a3754a68029d7ca54ed129a0085d7302c1c8cea96600b01900f34a76a93c1a7ac0522180330330af66aa294c3a45b3439b244a692b8114c8672c44178a200a5e56cd529a00b0665225a8445db9d2c3634005cc6540a826606261e056e9710958e46053544ab744a6829f1877e46b570a80b500207319961960eeb2946c94d00508f93151dcb62f1c15a00a6991990f524e76c2295003df291e108401807003cd8d22534329ca0664add1aa53403d8ca5069482d16d4b72a9287ac046b3501814400cc2c9baa534016ec923521e0dd6d54529a003ff31bf48840e652b34a2d69ecd529a01fee52395b44a68016bd0cd24aadcd929a023765218c1111a6e94029469438bd9a2530e8105be654dba25341fec866509b649204c6922706eb36d880303ab25aaa
def v4_25 := D 0x1805c800cd9d2caa00d4010fae479ba3006b1ab0f530ae6c94d00518f919601a0868ccc14c2bdd288a00d4036cd08604680d23521ce6d512833f0045b24a43320398d987753ba54d468020b1cc739b554a6027f396c8080c600cbc9daaa530e8138cd45a3b6964a602461aa4ee9129a0bce5033043441d6ce9120f672d005222412205709482124441ca15d2ae732b4014d20728810300400a5669cd529a00a5872a719b564a6802647cc6ce320032a636ea94d00480b952d9cbb2009cb4116cd51cea6d529a00a89f22a65290334876b2d88e7f6802994e536ac94d0050ef91722988ab14a44d924214e508090e4b04c8b1a7b95c40563b1814d1ce96d529a617008b297b5a540a3b4011e6e64b952db6233e5e00a4218256064a5eacd8250169a2b66a51bcadb253404dfd501900ee74b6bc94c046b302a04a80e912d4222c49e6d5b024e5a08b654696a0d172e74b6d81a8d014b344a17b96c919b4010cca694ed529a00988f319900b00ce34e1dd58ee582d684ab6802902009080c74201563161c5a56ad8443689408866aa1650d401a4203a943007d3cdaaa5340ae6a81348840e63661d25e8d529a022565298c98797ba4c468020dfcd286de5729a03d64332359d180380d807375b954a6802691cc73b544a681d5916be415ca4207851907d28403cc64c3949d5aa68482b4014d48e9d9a03cd230499a844813a3795b6ce1adc012a54ed1298577051b32cde9551969a0032f210d10771a3b96c4056265814d0c5ee95929a24fe052a0ea07ab7944a91ffb4014c63b5950b5aeb4010cca56dcd52980876ee33548f41290380c807a51b75e4a6021fdc883481d166cd69a055c3e5b331d8d6d7929a030644b82541141290527036b2d94d02a45b3482473341041982957a3b51e1a5340148b684c40e83a81d6e5d10c4722d00530d6dd129a0839f7320ce5080360d60795a3b5091b782b4014d48b912045aa880a784201c03801de56d383b74d019b24e00340101980297583b5594a6027198d8c25206546ce97202e72d005298c9874a19b54d4a8209d98cd003801d45eae5b10a26d00522051280368c92d16f2774a2280a773802982d0a2006654ed129a009df72523b754a64180bd9aaa
def v4_26 := D 0x2fa28801c46c43dd2c9bb2534013a9e4fc48460654a8dd529a2e7005238d387a7b94c45f9b4014d1ca96d7929a00687201df3424a99992490cc1ccd39a34fd29a00a637839981a44552885ad39dabf5d29a00a401c00f2f6b4a8021cb68029a9209b5006689631116c6af72c83d380209baa83a81cea55129a009bc73123521d46e8d50e47fed0052269cac13403609972ac4c38d62640a31300318979d8415bac225a759114eac8972da01582d0258b581140ac0eaa927a5554643c9d2dcbae75ab012d1fa04a00dc35c1d164ed529a00a55f2a35b95405a602c5985e8a2006654e9129a009e97207490803844a4088bb973a56e140561d029aa606603c93d1aa5340510ca421a20e2e764a94c3a046e798e7512ac94d0050d391662d487946a0271a100e94444953208a226a2e774c80a5838025a3a088c20d54201403801e8ded044369a003ff202c620032b476ea94d004cfb98350258064eade54369a00386520f9d2a03a09883d04a41e23264459d2dcbb6200928e814d4739b554a682a5916c94154200cd1cba25340135de63a109481847043c995d2e240cda00a4390250064ead5128ae7004633400e00775ba44a680290fc8e07cd06fa86801d33300e798049958735617a534014c10d1078273b50d4a6079994c943141e594edd85de802c3a053550d6e5129a00a5e5295613b69d4a602c593cd2daf25302f7ca68a1aa0e4f0b6bc94c01e711bc8e6d5165298874e5b31cd6d1298536047cf92cb9daa5340a98fd166a3952daf2534016fe4c72b6a94d003874598ea8256064c66d5790e6988b6402006822412a1150948393ab595c41bbb4014d24ae8d529a024c652020320032e734aa941b7602b998d6ca100601c00ee636aa828b68022d920cbdd3600adbda00a6a86b4220065cd69129a00a7ff2104a8a08b1a3b952bd882c15a00a600ea84019a71b9264a6020ef875e4538e602049080510d107965b736e0da61d2899a0f2e8d13284c46412220e11b1822dd58d26df904a6d00525c487164420f9a3b43c1d3010cac6d01220330ed6b4d87a7536802910d3d9b06a530e8087e6a398daaa226da008b6431c30ea656f2c94cd5780298448244066569ecdb38e59040a4362e400656ae5d5007f6008c668f74a894d0051c793add1aa531aee00a639d2daa534013b8e461c60f0b6e8228030043af9aaa
def v4_27 := D 0x1d1e420e0b1931c0981753ca01782500c4d2005248c18d2c40c60a20265ce56d529a0082a7215851003894ac528b2953a54a68028cfc803801da8ee571180ed00534a37b55514a68018dc85554200cba9d5a86a53405ecc73b54097d340116c86584a40ccbac59b08ad195a00a6a1800d181a46a43bd2da253400b1d52ae76a94d0047c798eb2876c14b4a8020bfc89984a40ccb1dd2e2051da00a68e6a556c229500733292c6ac3ba95d2a5340326ca629dbcaa48b4005cca41680680ae52905274b72a9a8cad005354288a9510b5973ab695a68025430add3625128104de604704381cdaaa53401219e43e23500601c00ee7562ac833368025a3d1dcae234005cca421a20f4b72ea94d00479f98d7b2400660692d4452a082766321300350334b2f6b9c8024a05352e32e1e855a5508474c0419b93195a2530362c8d663aa09501c4644393add2e21cb4116c803801dc8da6d5d29a054b51669316ae6c94d015f22d94a1dd2b232d34022ccb973566479faeb4014a18e96db04509408866aa531cdae2530162c82804a0f9ce407c8d200b628804d225a8c45b8cdd2a5340144fe541d40ee7752ac824f68025a426a9912804a90b064485412242930886154450b9420861d10113442c894c13372359226b991129cc488a062440b300900e0077a29b54d4d5680298e76a894d0045af90bc01a019659b35594a6815bd9a95a14ad4172e569c1b4c03232993acd1db25195e00a3662a5b9aa52ab4060c88d00d00dc31c1e8ee50af680ad00534682ab54a38bb0110c89d84c40d23521cdad65519645a00a659b2caa2eb40204ca40e822207389499116b2f74b3a8024b0053541685100388d887a953b54a6802a0bc88904880f0252079d3007844a4088b84b955ce3d6150298018a3206455ce952989e700521401311688900b344601ca43cc3d9a86a530e842cd2a15ed44529a033645642520621a20e756b2b88cd768029951950ee4d4b6d9cd004bf29307303cad59aa02b400f1c866a4628900197a25b5694a680cd951ba8db20cfda0096507503cad1dae2408da00a43942100601c00f3634894d02fb2819a346b43c9ad5aa5340147ce521b20f674b2a80350042b798a76e894d004f0b901258c019793b254a61d02299aaa
def v4_28 := D 0x80ca00c9c95d2a0d3da00be64fb8a200711b10f74e6b2c94d0051679409bd9304a530e914cd28e56d711a008864911e304849180526eb72a94d004d37992e374a8fcfa680b190c61840198b597364a61d1522d9a85a82340651a50f472b6a94d0048bb929539aa53374e00a622c5b9b253414e00a44980580671a70e756f2b88bb768029a289bda88a5400c4ca4771a6431d93114069803d07503dcad39b2531ee0540a6486483c3ad9d3608a3ac014a63261d04de6da744500600a6a94b16ea941e36800a9c8e34e1dd6ce9529a009caf3216adcd929a01e43af243ab7960168021238ccd1ce6d5529a25de45b292ab7364a68679814c6b01280336b52ea94823802319074015819529b73641f9b40110cd477d1900310d10737a51b641abb401293634200ca49ad2a534015bc327312800d0e482540a4eca5310e5808d6409a4421cc821052af746a94d002b329a44db9aa53080c06d65236c2351b401a82985b735460fd34014cb9857a374a6807979480f9d840702c20b01900eb30e76d88eb004b5516b20840cadb1baa00b40095ca4b16e6a94d11f80291140ad0890564169079ea101e3dcead65b384f6c04b432d5100388d8875b3744133b4016ec90b20840cc93d1aa5340071ca61c654f0c5cbdd2621a2caef0052b3975a64012b1b4014d4b8cb87378b55e4a60219bc923121ed1660d92a054868fcb309d058c5b02c00b4895a1116cb476f2f87ac20302549b8dab4ea530e916cd256e8d529a024b65273b544a6802c598d11a66690d2b34d0949a544a0266b2b3562ece5511e86bad005205c12a0318e1875ab795c401393c014d50d6e5d529a00a7df2573b44a68023e7cc77d128032c2f6aa94c830016f900048801886883a954bdb706d34056cd1d504880ec32c1e9465edb3a9808b656694b2ca34d046b0299136a6a74ba680792940640391d3cab4a02d3014cd48991201650840297895b50eda534066c94c6d11a009aa68b314e6d129a00a00f21a402a0336946f2c873fa802319a1bdcaaa5340146fe4040660065668ed4369a00a86614d59aa533b5e00a509c9a9204c90d2706af36d812f018025aaa
def v4_29 := D 0x5b9d4ab2534013afe4e04a420309110510d1071a5b4c09143b40148e34e1da8ee571015882e0534a7b444a68209d88de4981e600691a90eaf566aa29500417f9831c30f2c476a5abc9a602299507503d29dbcb202c8b4014d473ab254a69e78114ca5c6e96569a00a06600ea84019a8b9254a6020a790c89e74884c4a420a526ce97194afed00534358a98b0b9873b5114a8965814a4ae8d529992f005325d6acd929a01eb65208cd2b0308e087975ab5094396820dfcd52965ced92980a8b6a10d1074259b36094a682247cc7bc9100308e08723b744a687f81219e492774b880ad001979a1c955a914d29a00a4b472ea814768022198a29476d88d00fa32908f28401943ab596c0568150199a8a5472ec94d00538f928da1aa54010d1f96651e5a83c5c1b2dae7649eb014a43241c49ee61b10060084e73473b544a680291fc8d405a86a82d230a12907a0ea076b5973a740c3b4012c5451280360e60785b7354a6800b99f2e4c6b74a828f25602219aa892774a80b4d003e394951baa532080c8ca645b8654304028052b536e6c1a94d001279a42c99a01ac6ac3ad3d9aa8a34010aae421025806b1ab0ea6f56a94d007a7298dd24420661c60e47572a829768079290b60160199b3a445c782b4014d4b8cb87a659b5cea6029e1c90d6e5529a009b6f3252e8d51969a0077f210d107a3b94c43adb4014d0c38c1dd4aad4452a0054652824ac148bb97a354a6802633cc90c907497b386c7a3a3ac0149692ab122e569cd5004e495040a6a931b30f24f46a94d0140b292ba31101ac6ac3ad3d9aa5341f9c0a64c2db9b25340429ca458a35012a108054404790c110f5a73b511382b4012d28de6d711a0087af2359d181e68840296325954a6802663cc04cb180348d487a92b754a67bdc01483600cc1a86640a5526acd945015a00866a298dbaa4d3da008b649f966006b1ab0f0a76eb3294d018331c38ea0e19f40000590079a4a4c48b973a5b61109a820f9a863861dd6e913506e6d00534639b554a68028f3c9cead5529a018268b300b4888cac8440a5269cd529a1e06052a90b6364a61602359aaa
def v4_30 := D 0x163561e5ed695004a8ed00525501282aae8c02c06c03a9b4baa5340145fe591990ec54772d88bfb68029a3a8d0401c06403c939daf06d3011ac83604a491ca100a91a90e772a89419f802219925746a94d0fdb0290c820c018907837b95401050f1c014d4c8cc87a36b95c41e9c0104de4a5356ec94d00433b9803be6876c7333b5219839725a3b6835a53401480004600d43541dc66d69b2d5a00866696b26ea94d0052bb91440990ef04a4021a420f14aca962a55a52736eb4a94d0077b299356e6af57a6802199459acaa1e82b080c0a6a9254f66c94d44707929086883d1dacaa39bc15a00a6429bdaa53401437e454c2520621a20ed4772b886ff68029a52cdbaa5340119de45f826a06486d8d529847e054b31168de1929a01f1e2d79082e9501ac6b158b985ab7639ba0092c014d4c0cc07a37b5964453b401285f04680d23521e60ed552833f004e331d41cac0e03201caa56d71a78f580a42802621ecb300f029407a14803c8a3016521c85ee8d82529874a16694a366ec94d00522f9446c43dcbd1aa534030eca60c70c3d25bcaa488dcda00a512c6b74f884ac2044335516754200ccb91daa5301148bce4654af2c94d0112729528cdbb600b40116cd21300d4e4aa320a6a58ed444369808d654f6a894d001e711bcca7b944d5680241bc843441ca6dcd52987454824f35023821ce56d312776d005253d92003488aa510bb3a9554a68026d5cc0259200122880295943b54a680214fc88c84a40c43441e8ee531174ed0053437b9554a6802939c8e444200ccdd1a53401316e866535caaa53060c0833726835ba6c2560219219aa478095819382b950d4a602135ca5c6e96569a008fc730e34e1e68ed312146d00522b432b10e08d0ac94401ca1d2dae04b40152cd145e8ed861694d00523c9108032a506ea94d004cb798c1cc0f6f34aa94d004f73906449401886883cad9baf2530e857ca6a3e2999a2b9cc51520628a4b300958d5876735b52afa04cda00a531b30f48736a9a950046331c170d0e080580aa93cea990f1f572e99d6a7ac052a58b7511401800e194d223221d661cedb1239f004a73b544a6802719911b10eec72b6c94d004eef900af9580404ac02a646010d23002e8d00214c4018a32005118112f3674a94c1bb8029aaa
def v4_31 := D 0x28b20032b4f66a94d004ecb9128288019953a44a68028d5c8d0008467ae320a65a14dd928960038e534531b754a68022d926899985414441563561e9d6d02529a01b6653daa534013fad09f2693b5a620580d4010ccd435b9754a6802135c864ee9529a009bff3283a81caade5712116d0052673b55ea61d02a19a50ca5ae234104ec865374e6a94d00f35b310e56d7045e87ac052095130033366b4a87a0ac3cf029aa54bd9aa534051cca4b3166029a1282c909016384602603601dd8a6d596529a05616651b2dae23444e00a401c00ea2f572d8833368029a249dd2a6a222da00a4a752ea94d1380221983782220656e9cd529a009067212d5280a64900526460289e20125a49ed5b92987456166a394d2aa534014e7e491890e8b166aa29504347e59951950e94f36a221b4c82053268d6876a3b95c405602359a3fef88019317b554a6802927c8e500d00406600a6561cd428694c04e3307085200f349c5cb33509911c5d65e0edb025d6009572b4e4c94c2a03b7719aa94772894d00e8f295ad1cbb253401452e4cb366a134d02a54334a9823b6095a53011ac91b7cd08d286801a43300c0180497639b56695a534014ca7b944a680241bc86100d00e03201e9ae5125005808d66a251dcae222dda00a4cae76a94d07bf28d9936689047a68020adca63261d52e4e9b11a008c9f3404c6200334b6e6a94d00528f92b59baa533ec05ecc38d387879b3a6c46175802903669801cc64c3ad1bdcb6200aac0a94d5260ad8d92983d484272932ba54a680271fcc953b44a68085fa2c863861d65ee97100579f0053482883303325476a4a34a6802900ef9a0f81ccc7b90660e6568ed59c694d0053250ead711a006065273ab596c018020fd8ccd4a97b354a6809ab949e54e9529a009adf30820484e346407161200732b476b81272d048b200e00793ba44dd1a68029a2cd9baa5340147de541d40eb72e896b22d005308c06680f348c1266a11204d8e9e56df398ffe04a932ba54a6802f99aaa
def v4 : BT CertNode := BN (BN (BN (BN (BN (v4_0) (v4_1)) (BN (v4_2) (v4_3))) (BN (BN (v4_4) (v4_5)) (BN (v4_6) (v4_7)))) (BN (BN (BN (v4_8) (v4_9)) (BN (v4_10) (v4_11))) (BN (BN (v4_12) (v4_13)) (BN (v4_14) (v4_15))))) (BN (BN (BN (BN (v4_16) (v4_17)) (BN (v4_18) (v4_19))) (BN (BN (v4_20) (v4_21)) (BN (v4_22) (v4_23)))) (BN (BN (BN (v4_24) (v4_25)) (BN (v4_26) (v4_27))) (BN (BN (v4_28) (v4_29)) (BN (v4_30) (v4_31)))))
def v5_0 := D 0x28cd2980aebea736544abf95ce009653c922530e876a9ced2973805884e4b465974412fbac012ae54f3aa06c04b0c59511a02bf64a75183b6c09165c0129e6e91291ed004b54195b4ce49db012a54ded52a00aa36b16ce1312c77004a010918006a8802a46a43c13da28a530ec2ad0c59511a02d868aa2a5b4ce251a5812c95b344a615d938a8656d339881e04a5ba635110d05250215aa800024407252105274b2997276802542b9a25301551d6013094819793a44b2db401296add106b7500dab49365445d29bc01296d8dd7830ec3a04b145cd11a00abb6aba6944a60f591aa80204440ca2dc22009cc036ad52d64f3adf6c04a58b74401a80163ac85b744ab09c036a8c59511a030368aa008119033056e880343a0dab52694d29a0551aea29634405600ef94ac97ba44ad7b4012ade95129a02f1ea5b974ceb56025aaa
def v5_1 := D 0x10ae6894d006b753995a25301567d631caa25a0da0094432f6b812f018025a51dca20a5d808b96a29b74149a00c012cb56344133b0138aa15cd29a030264a69b34462e18110ad500004880dca420a69e4f2e26d004a018d08032c774880b52780258c652894c0564f538dd2202b407ad1568876b4b9c8030d98129ec56572d483ec04b256cd2833f005b2a316544680be79298e55102f6d004b55215cd129a02e7ea95a344aab18162ac03e520032b6e69491b808552d49a5340aa07d68c32a894c2fb2c550cbda6700904c0961934a204fd808d54cb6616be2ddb012a5ca9111ced004b54a5b3ce3d606d53c9da6200a3fe0960b5122530769aaa96e533804e7604b405912802728801194201cc3ad2223bda002a6a3b154096823c9c0ac75a344a602ae1aade95129a02f56a857344a68025aaa
def v5_2 := D 0x42b9a25dada00946b2e8958f6802592b6689500567b528b9a2340152ed68d6b4996e73d6025009094019807b65a95c40f7c0a92c632b44133b0114a9e6ad30074d004a01ba41b7a02b014ad50eacc4426a0b954a552ebc1876802586eb689647680252c6ac3bdac26200c036ad1cd651115ed004a639544a75b4012c639244a60b13553a0da254104ec26ea7365445d68025aa8c6b2888a7680250529d3401555d62c6ac3cab9daa4a00a40c0940392400199180528d28717b244a61d152a9ad1d4e11049eeb004a9653a5491147dc012c73a544a680af3a8ea6d129afc604a53b795cea925025aa52cda0884d41092d50ae681b4d0150f58eb4689500417f53194a2530160ad40a2f6a8030047f75a8092a5004652002108c03927a544a68b57854d4f2369880314cb258c6b2ea8383614d812a08d912980af3ea002129032f2748818768025aaa
def v5_3 := D 0x3195a253015e0d48b26cb921476802592f749693a680252d9c26216de00968c652894c04933500009100c9484149d2ca6167da00964b8d22534583c95304c76c221b40426b5460939120247d2cb9aa0082928e8aad5149cd026990c641af5318aa254dda00963194a5301243d256aa7b244a61d00a9ad1d60d10586eb004a3b694c60219093ac639544a680b1551a4a2094da0094ca72f6c87a0ac3b1ab55215cd29ae9f004a857344a680ab9aca7b244a61d0163aa6d4d29a055056b49765445d411c012ae54f39a9ee04b256cd1033f00416354b1da04a24defdf04a5ab341151a82e55aa3dc9e5c1cf58094c6528951760235592f4a894d0162b529b5a64a0092812d1e56912d7ed004a85b975ce403b012cb7a544a6806d542b9a234015ecd4b6e6822120307b725aaa
def v5_4 := D 0x25ee912ec6d004a631544ac3b4012c639544b39b40129cd951174ae7004b4736544b6fb40128a6dd080e803004b00394200e03601d4ecd2506bec04a639544bfdb4012943541de6cf380692e04b54952ab5ce6042d92a5ecf080e03004b18e5512c7ed004a843ab76114129928e92d1d68d12980ad96a5b974cea71b012ca3b94414bb011aa8ca8d2982f866aab69a254475b0110ad54753a44b95b401298e55129a02a9eb18ca512980acc6a9a534a68150b7ad01a74880cc2420a64e0f057eeb004a02a12100028c8290573409a683bd92c17a544a680af1a9842d129882766aab733110da815e55aa2931baf061d9040954b2e6b843b60218c62a8961b6802501608d019a94344107c015ca962dd100600f4e4b51ce95129a02d4ea5ba34c0965684558c72a895b76802531caa25e5da009400024400252105274b2982bf68025aaa
def v5_5 := D 0x3a1b44bbfb40129d4e9105875a780258f2b48968b6802500869401980791b7586c4018a6192d258a9128aee0419b5016a888194ba34a2546395cacb7a544a68b05b6a9c6d6973917e41302534d9a2323cc08856a90ae6894d0171b542b9a54be9a009651dca082e9808b96a3a1b44a4fb4012d01774a80cd194a25b6d84c604a729b55ec9b5602596f4a894d0091351349a53015f5d40080520731930eb672ea9a8724a3a4b55104e912e8ed004a857344a680ab5ac632b44483b0114aade4c3406003864b4631544145b0162aa52e8d70246bec2a4b2e961d5027ed00daa453b44a49fc060a966dd3164e588b56a8b47699d703602555a9a5128116cd64031a2531589cd552ac76b92024a043405912002a88c0145440092a10125d6cc6f74d0015350000118195b734cea69b012c17a544a6802dfa85e95129a033556f4a894d001535aaa
def v5_6 := D 0x42b9a253405dcd50ae688d005597590ae694d00447352cd9f06d30a96ad18d65d51246c29b02555bca609ed840604b09e4d2980ac06a71ba44c05b4012962cd101433f0042b54743a44a682b87a98c551067ed004b00c84a40cbc9d22592da0094c72a881cb68025a3d0da25b4da0094e54a9812d04127594b6e8227a6806d53194a25015f1cd54cb749884b47f025aa8c72a9737a680253ad1a2534556f0562dd1a51281225d5536689508f72315a033294819a79340c3b098c094b1ab0f2ae76a9212f0180258e8348950413b0bfa945ed0b4682cb8025003284019b9537543d6a43812d50e56d33adfec04aab974e13792b012c85734468020b1aa56cd12a00b066a5b634405600efd6ad40515280272900297a534a6b598054d5296689419f1d22d596e6b0a12f1c1b4012a56cd12a00af46a857344a680c15aaa
def v5_7 := D 0x18c5512f0ed004a753a441618b7e009639d2a253405a6d531930ef6749822122e7825a31caa25bcda0094004242034519052ae66134d078b258c612894c490b3553cada706d300fad501900f2b56893c024a04b5473b31109a82275a9d6cd12a00aa7eb2de95129a02ca6a75b344133b40adead21499129807478aa5b6375e0c3b3e812c85734a6802d953ad1a254010abd50b366b8b27ac2a4b5501c84a40cbc9d225d5da0094cb26eab2187680259256689419f1d229559aca00a0be008656856d2988ea046aa00252103350872b94fb6802596e6caa95f3680253a8c1db168c24597004a58374401a80c15aa49b5a04a24dd56094a56f2a1dba68152d58f53689633680250062d081b8a5633928f3ab4954129928e90d25cd6d46f74d004a853744a680a6dac852744a680ae5aa56cd12a00af6ea75183b6c09758025aaa
def v5_8 := D 0x8a7689493f02b954b51a25301560d62d9c262163e00946f6a894b768025a4ad985af8f580942eb6830709780c012c95b344a802affa945ced6750597004a97ba44a49b4012d528ed657025a07764a596b4c401a8f812c5379445d2b3c012a1ecd03529874eceb47a5944b63b401296e8d2894090eeb296dd1285bf00daa95b3ce6bdf812ad0e9101494040e42b5516ce1311d60094074252065e4e912a96d004b2de95129a02cbea639244a55b011aad2e54c2d7d6ac04a73b4a5ce016a7792c631544aefb4012914ed12afb7004aba33c09010dbc12d5146de57083e7ac04a039118000a880299a330da6803bbac639544b0bb401285ee53046981f80250c70c3abd5a608bc0494096a318aa25a8da0094a1aa0f2f679c034c702594772895b3680253194a253015e4d46b2e8814768025aaa
def v5_9 := D 0x2d9e512ef61e3802512d38aa0b0dab4604b1ce95129a02d0ea00d12803300f12b6eb88034bf025a0b14a26ab01066d4059e50064dc69567503df02a4b25a8d12980ac0ea9468354ac0b8071c94c42e88c3a4887219ad501b84a40cbc9d225c5da009403ca10066e9d455015aa5604b2dcd61425e927680252c5ba200d40054d680c024405e5210526cb2816b2cfb40129d8ae55b3883ec04b18e492980921e6aa95b344a802be9aa3049c890123d5e8d100594947496aa411ba253015d0d4c6a28956768025925668943a8cf2295255ca25452cc8c5690a868941b380c15515cbae753cd80963a0d2234104ec2c6a651b44a6bf5962aa5ca9111c6d004b5492b3c09396235514bda6200a40c09651b4a253588c8d544f728221a0b01f2b4a9b344a4798111bd54b6e6b9c37760258eb46894c0447b53195a253010d4d46eb68813368025aaa
def v5_10 := D 0xea748976f6802501ae950193a7944ac9b4012c75b344a802237aa83a81ee54f047ad40968e24c88d0056eb53d99a530e922ed62c3da251dce01b54e74a894d0180752c59a202b03890ad516acf38e588b548b346a121876802586eb6888db680252d9d2620d6e00968e74a894d0061f54d29a5340aa1fd64ad9a64d30138aa8859128b06046aa98c9875b634d425391812d54853744b99b4012a558d1120ec04e2b00f30a80c8bada0c3d03df004aa35b95c117dab012d01a04a80cc9d1a09bc367004a7653b5ce1adc012c635944a602af5a98ca512980afceaab594c0155811f92d5256cf38b76c04a5b9735e13786dd809629cba204fda009474368982f6802535aca602b40a96ad4a9b344a2e18124bd4736794cf0180258ec6b2a95bb680254ad9a254011b3d50ae6894c0441b5aaa
def v5_11 := D 0x42b9a234010aad4b52e881471c9c012c359744b4bb4012a1e55100600911eb4962a495a6020cda98e5512a0ed004b28da512991ee46aa537b4e0da601fdaa5cee95b02404947496a8a4e681213f6820d7a80874a80442520a4e96512a76d004b18ca5129809256a639544a53b4012d162dd129d601b54a572eb96ac20302592b668950055d354b95220c9da0095389499116b6f46b3a8024a3a4b550d65d12ea6d004a856344a602abbac58b74401b35c01292ae512a0ff6462b44365445d2d3c0128696d31808b69563194a250157bcd5432b697f3e49db01294e92552916d004b5441ab35594107aac1289c6d5506aed02a5ab18e5512980ac5ea78c78797b3ce0125025a3ad9a2540124bd4c72a894d7680258e76a895c7680253a8c1db60496de009570e6880ac55b0295aaa
def v5_12 := D 0x31caa253405d9d482748958b680258f43689677680255bd2a253400b1d690ae6894d056e35007294019807ab594c41afb0a92c0121080380d807573b44940f7c0129d6cd12a00affea60e607597b4e1718092812d5258ed339810be4a0165080334476880ad5230258eb668950056435529b5cb620092971c968c72a896cf680250120910009484149d2ca6539da00964ad9a25310bc1c546c56812fa60235531c922530109ad6aa42b9a253405cbd46b2e89553680258b1ab0f2ae76a928028ff82500a49001949b244a61d150b7ad0ee49026984c6542a58d5877285b5ce01806d596f0a89434b806d54951a253015f7d426f69812ab041bf5aa4abda604b4214c94a9346b950b680258eb6689500561f55bd2a25340609d4ea756b8120ad15ab5215cd29a2d5604a7b594ce013ab812c97ba495a6802531caa25e6da0094e72a8824f68025aaa
def v5_13 := D 0x857344a602455a96a5d1028f5ab802592e748968f6802559cb2aa00c0116cd68c65288c056ef499a8d68d015a00fe6b256cd12833e058aa973b4ce60215baa48ed11a936046ab54823744a602b8fa9d4c129a00aa66b1d8d655124ed004a639544a51b4012d01874a80cd1aca209bd830604a51ab3509410786de09631c9225301172d4eb668950041375004014019a3b7499401391d25aa90ae6894d0174b531c822531242eadeb2694d29a0551a6a9b73401802413ad2850d1283660572a94ba35c090f7c0a92c326944a48b811aa94c6d11136c058aa3b59449eb56025aa314daacce49eb012ade9512a27500dab1ce551123ed004a6297b5ec90125025a5c9d253170c0ad76a397b4ce010d9812c17a544a680ed51b24a25ebda0094c652894c042135aaa
def v5_14 := D 0xc72a89777680254bd2a25340566d629cba259fda009541d40e72b498228fb8025a52dba250b7e01226a5b6340da6019093ac583744a48dc05eaaa5cd129a0b01ea62174461d244190cd6a9530ae6d843b61602539d2a253400d0d61d3ca2248da0094c72a881d368025a39d2a253405b5d52d6b4b8cad045ab28ee504174c046aa3641446802be5a863861e5ecf3804e4e04b551ce5512e76d004aa57344aafb4060ac51b944a602b33aaa6cd12a95e0462b4847344a68213e0a8e5ed03480e03004b296dd12922f00daa65b385c4165c0129e86d106aed004b547a3b41109a8242ba8ee55384dec3a04b18e491123ec046aa42b975c0125101812d01544a00842100a5d68d2ad6f0015351dd12604b0e952ac32a4954adfb4012a15c9129a02f4ea856344a602c55aaa
def v5_15 := D 0x18e55129a02f16a7543a54161b183c09631aca253015a7d4f5679c0ac052b4632944a602b7ba8828ed71847e054ab18ca5129808d54772c822940426b5002888019759ba5401475c012d514ee110e6e47004a857344a680aa1ac632944a602b2baa52cd12833e3a4e2b497356545d2cdc0129c31c1d2ac5103decb02a4b1ced512baed004a07550803356e694d01eb6d53add2200d20e0096aa5b3ca25d6c3c7004a02a1290332eb48957b680258536689500566f538daa25340aa0cd6856d0988c017335545caa67353fc096318aa2340157dd4a2e76b7f74165c0129e569111ded004b54259b4cb859eb012a4528d5298749166b18c5512c6ed004a0101a203510aad5441eb36c6a8024a5c721a159b208a501084d404024400252105274b2994df680258c62a88d0055cf531a8a234015eed476b098d00173195aaa
def v5 : BT CertNode := BN (BN (BN (BN (v5_0) (v5_1)) (BN (v5_2) (v5_3))) (BN (BN (v5_4) (v5_5)) (BN (v5_6) (v5_7)))) (BN (BN (BN (v5_8) (v5_9)) (BN (v5_10) (v5_11))) (BN (BN (v5_12) (v5_13)) (BN (v5_14) (v5_15))))
def v6_0 := D 0x2419a083e0304462a642b4a1b010ad58d10049708e4345733cc3fb010928cd041e3a57230e54d128f186f214c6cc3b29da26a60ec9486a2d99a621e0084ae678d8570218ae6643f6c3b81090ecd0049707e4344733e137b109c84ae67984f6021872a68947c33810ad5cd10e49706e43545733c6c2d81095ccc87f87b802159a4a2610c9474868a867c26f0d981095ccf30a6c04315ccc87f86b802115b9a009c8eb68d45733cc41b01095ccf1286c04315ccc87ed8730212c6ac3b29da4ca00971c868eca616b21db01095ccf3096c0430e54d30c7185f212b99e10ed8086aa
def v6 : BT CertNode := v6_0
def v7 : BT CertNode := BE
def v8 : BT CertNode := BE
def v9 : BT CertNode := BE
def levels_W5 : Array (BT CertNode) := #[v0,v1,v2,v3,v4,v5,v6,v7,v8,v9]
theorem w5_slices_ok : btAll (sliceOK 6 tgt_W5 bases6) slices_W5 = true := by decide +kernel
theorem w5_syms_ok : btAll (symOK 6 tgt_W5 26 slices_W5) syms_W5 = true := by decide +kernel
theorem f0 : CF 0 v1 v0 = true := by decide +kernel
theorem l0 : btAll (checkNode 6 tgt_W5 10 0 26 zs_W5 slices_W5 syms_W5 v1) v0 = true := btAll_mono (checkNodeFast_implies_checkNode 6 tgt_W5 10 0 26 zs_W5 slices_W5 syms_W5 v1 (by decide)) v0 f0
theorem c1_0 : CF 1 v2 v1_0 = true := by decide +kernel
theorem f1 : CF 1 v2 v1 = true := by simp only [v1,cf_nd,cf_em,c1_0,Bool.and_self,Bool.and_true,Bool.true_and]
theorem l1 : btAll (checkNode 6 tgt_W5 10 1 26 zs_W5 slices_W5 syms_W5 v2) v1 = true := btAll_mono (checkNodeFast_implies_checkNode 6 tgt_W5 10 1 26 zs_W5 slices_W5 syms_W5 v2 (by decide)) v1 f1
theorem c2_0 : CF 2 v3 v2_0 = true := by decide +kernel
theorem c2_1 : CF 2 v3 v2_1 = true := by decide +kernel
theorem c2_2 : CF 2 v3 v2_2 = true := by decide +kernel
theorem c2_3 : CF 2 v3 v2_3 = true := by decide +kernel
theorem f2 : CF 2 v3 v2 = true := by simp only [v2,cf_nd,cf_em,c2_0,c2_1,c2_2,c2_3,Bool.and_self,Bool.and_true,Bool.true_and]
theorem l2 : btAll (checkNode 6 tgt_W5 10 2 26 zs_W5 slices_W5 syms_W5 v3) v2 = true := btAll_mono (checkNodeFast_implies_checkNode 6 tgt_W5 10 2 26 zs_W5 slices_W5 syms_W5 v3 (by decide)) v2 f2
theorem c3_0 : CF 3 v4 v3_0 = true := by decide +kernel
theorem c3_1 : CF 3 v4 v3_1 = true := by decide +kernel
theorem c3_2 : CF 3 v4 v3_2 = true := by decide +kernel
theorem c3_3 : CF 3 v4 v3_3 = true := by decide +kernel
theorem c3_4 : CF 3 v4 v3_4 = true := by decide +kernel
theorem c3_5 : CF 3 v4 v3_5 = true := by decide +kernel
theorem c3_6 : CF 3 v4 v3_6 = true := by decide +kernel
theorem c3_7 : CF 3 v4 v3_7 = true := by decide +kernel
theorem c3_8 : CF 3 v4 v3_8 = true := by decide +kernel
theorem c3_9 : CF 3 v4 v3_9 = true := by decide +kernel
theorem c3_10 : CF 3 v4 v3_10 = true := by decide +kernel
theorem c3_11 : CF 3 v4 v3_11 = true := by decide +kernel
theorem c3_12 : CF 3 v4 v3_12 = true := by decide +kernel
theorem c3_13 : CF 3 v4 v3_13 = true := by decide +kernel
theorem c3_14 : CF 3 v4 v3_14 = true := by decide +kernel
theorem c3_15 : CF 3 v4 v3_15 = true := by decide +kernel
theorem c3_16 : CF 3 v4 v3_16 = true := by decide +kernel
theorem c3_17 : CF 3 v4 v3_17 = true := by decide +kernel
theorem c3_18 : CF 3 v4 v3_18 = true := by decide +kernel
theorem c3_19 : CF 3 v4 v3_19 = true := by decide +kernel
theorem c3_20 : CF 3 v4 v3_20 = true := by decide +kernel
theorem c3_21 : CF 3 v4 v3_21 = true := by decide +kernel
theorem c3_22 : CF 3 v4 v3_22 = true := by decide +kernel
theorem c3_23 : CF 3 v4 v3_23 = true := by decide +kernel
theorem c3_24 : CF 3 v4 v3_24 = true := by decide +kernel
theorem c3_25 : CF 3 v4 v3_25 = true := by decide +kernel
theorem c3_26 : CF 3 v4 v3_26 = true := by decide +kernel
theorem c3_27 : CF 3 v4 v3_27 = true := by decide +kernel
theorem c3_28 : CF 3 v4 v3_28 = true := by decide +kernel
theorem c3_29 : CF 3 v4 v3_29 = true := by decide +kernel
theorem c3_30 : CF 3 v4 v3_30 = true := by decide +kernel
theorem c3_31 : CF 3 v4 v3_31 = true := by decide +kernel
theorem f3 : CF 3 v4 v3 = true := by simp only [v3,cf_nd,cf_em,c3_0,c3_1,c3_2,c3_3,c3_4,c3_5,c3_6,c3_7,c3_8,c3_9,c3_10,c3_11,c3_12,c3_13,c3_14,c3_15,c3_16,c3_17,c3_18,c3_19,c3_20,c3_21,c3_22,c3_23,c3_24,c3_25,c3_26,c3_27,c3_28,c3_29,c3_30,c3_31,Bool.and_self,Bool.and_true,Bool.true_and]
theorem l3 : btAll (checkNode 6 tgt_W5 10 3 26 zs_W5 slices_W5 syms_W5 v4) v3 = true := btAll_mono (checkNodeFast_implies_checkNode 6 tgt_W5 10 3 26 zs_W5 slices_W5 syms_W5 v4 (by decide)) v3 f3
theorem c4_0 : CF 4 v5 v4_0 = true := by decide +kernel
theorem c4_1 : CF 4 v5 v4_1 = true := by decide +kernel
theorem c4_2 : CF 4 v5 v4_2 = true := by decide +kernel
theorem c4_3 : CF 4 v5 v4_3 = true := by decide +kernel
theorem c4_4 : CF 4 v5 v4_4 = true := by decide +kernel
theorem c4_5 : CF 4 v5 v4_5 = true := by decide +kernel
theorem c4_6 : CF 4 v5 v4_6 = true := by decide +kernel
theorem c4_7 : CF 4 v5 v4_7 = true := by decide +kernel
theorem c4_8 : CF 4 v5 v4_8 = true := by decide +kernel
theorem c4_9 : CF 4 v5 v4_9 = true := by decide +kernel
theorem c4_10 : CF 4 v5 v4_10 = true := by decide +kernel
theorem c4_11 : CF 4 v5 v4_11 = true := by decide +kernel
theorem c4_12 : CF 4 v5 v4_12 = true := by decide +kernel
theorem c4_13 : CF 4 v5 v4_13 = true := by decide +kernel
theorem c4_14 : CF 4 v5 v4_14 = true := by decide +kernel
theorem c4_15 : CF 4 v5 v4_15 = true := by decide +kernel
theorem c4_16 : CF 4 v5 v4_16 = true := by decide +kernel
theorem c4_17 : CF 4 v5 v4_17 = true := by decide +kernel
theorem c4_18 : CF 4 v5 v4_18 = true := by decide +kernel
theorem c4_19 : CF 4 v5 v4_19 = true := by decide +kernel
theorem c4_20 : CF 4 v5 v4_20 = true := by decide +kernel
theorem c4_21 : CF 4 v5 v4_21 = true := by decide +kernel
theorem c4_22 : CF 4 v5 v4_22 = true := by decide +kernel
theorem c4_23 : CF 4 v5 v4_23 = true := by decide +kernel
theorem c4_24 : CF 4 v5 v4_24 = true := by decide +kernel
theorem c4_25 : CF 4 v5 v4_25 = true := by decide +kernel
theorem c4_26 : CF 4 v5 v4_26 = true := by decide +kernel
theorem c4_27 : CF 4 v5 v4_27 = true := by decide +kernel
theorem c4_28 : CF 4 v5 v4_28 = true := by decide +kernel
theorem c4_29 : CF 4 v5 v4_29 = true := by decide +kernel
theorem c4_30 : CF 4 v5 v4_30 = true := by decide +kernel
theorem c4_31 : CF 4 v5 v4_31 = true := by decide +kernel
theorem f4 : CF 4 v5 v4 = true := by simp only [v4,cf_nd,cf_em,c4_0,c4_1,c4_2,c4_3,c4_4,c4_5,c4_6,c4_7,c4_8,c4_9,c4_10,c4_11,c4_12,c4_13,c4_14,c4_15,c4_16,c4_17,c4_18,c4_19,c4_20,c4_21,c4_22,c4_23,c4_24,c4_25,c4_26,c4_27,c4_28,c4_29,c4_30,c4_31,Bool.and_self,Bool.and_true,Bool.true_and]
theorem l4 : btAll (checkNode 6 tgt_W5 10 4 26 zs_W5 slices_W5 syms_W5 v5) v4 = true := btAll_mono (checkNodeFast_implies_checkNode 6 tgt_W5 10 4 26 zs_W5 slices_W5 syms_W5 v5 (by decide)) v4 f4
theorem c5_0 : CF 5 v6 v5_0 = true := by decide +kernel
theorem c5_1 : CF 5 v6 v5_1 = true := by decide +kernel
theorem c5_2 : CF 5 v6 v5_2 = true := by decide +kernel
theorem c5_3 : CF 5 v6 v5_3 = true := by decide +kernel
theorem c5_4 : CF 5 v6 v5_4 = true := by decide +kernel
theorem c5_5 : CF 5 v6 v5_5 = true := by decide +kernel
theorem c5_6 : CF 5 v6 v5_6 = true := by decide +kernel
theorem c5_7 : CF 5 v6 v5_7 = true := by decide +kernel
theorem c5_8 : CF 5 v6 v5_8 = true := by decide +kernel
theorem c5_9 : CF 5 v6 v5_9 = true := by decide +kernel
theorem c5_10 : CF 5 v6 v5_10 = true := by decide +kernel
theorem c5_11 : CF 5 v6 v5_11 = true := by decide +kernel
theorem c5_12 : CF 5 v6 v5_12 = true := by decide +kernel
theorem c5_13 : CF 5 v6 v5_13 = true := by decide +kernel
theorem c5_14 : CF 5 v6 v5_14 = true := by decide +kernel
theorem c5_15 : CF 5 v6 v5_15 = true := by decide +kernel
theorem f5 : CF 5 v6 v5 = true := by simp only [v5,cf_nd,cf_em,c5_0,c5_1,c5_2,c5_3,c5_4,c5_5,c5_6,c5_7,c5_8,c5_9,c5_10,c5_11,c5_12,c5_13,c5_14,c5_15,Bool.and_self,Bool.and_true,Bool.true_and]
theorem l5 : btAll (checkNode 6 tgt_W5 10 5 26 zs_W5 slices_W5 syms_W5 v6) v5 = true := btAll_mono (checkNodeFast_implies_checkNode 6 tgt_W5 10 5 26 zs_W5 slices_W5 syms_W5 v6 (by decide)) v5 f5
theorem c6_0 : CF 6 v7 v6_0 = true := by decide +kernel
theorem f6 : CF 6 v7 v6 = true := by simp only [v6,cf_nd,cf_em,c6_0,Bool.and_self,Bool.and_true,Bool.true_and]
theorem l6 : btAll (checkNode 6 tgt_W5 10 6 26 zs_W5 slices_W5 syms_W5 v7) v6 = true := btAll_mono (checkNodeFast_implies_checkNode 6 tgt_W5 10 6 26 zs_W5 slices_W5 syms_W5 v7 (by decide)) v6 f6
theorem f7 : CF 7 v8 v7 = true := by decide +kernel
theorem l7 : btAll (checkNode 6 tgt_W5 10 7 26 zs_W5 slices_W5 syms_W5 v8) v7 = true := btAll_mono (checkNodeFast_implies_checkNode 6 tgt_W5 10 7 26 zs_W5 slices_W5 syms_W5 v8 (by decide)) v7 f7
theorem f8 : CF 8 v9 v8 = true := by decide +kernel
theorem l8 : btAll (checkNode 6 tgt_W5 10 8 26 zs_W5 slices_W5 syms_W5 v9) v8 = true := btAll_mono (checkNodeFast_implies_checkNode 6 tgt_W5 10 8 26 zs_W5 slices_W5 syms_W5 v9 (by decide)) v8 f8
theorem f9 : CF 9 BE v9 = true := by decide +kernel
theorem l9 : btAll (checkNode 6 tgt_W5 10 9 26 zs_W5 slices_W5 syms_W5 BE) v9 = true := btAll_mono (checkNodeFast_implies_checkNode 6 tgt_W5 10 9 26 zs_W5 slices_W5 syms_W5 BE (by decide)) v9 f9
theorem w5_levels_ok : ∀ (d : ℕ) (hd : d < 10),
    let nextLv : BT CertNode := if h : d + 1 < levels_W5.size then levels_W5[d + 1] else BT.leaf none
    btAll (checkNode 6 tgt_W5 10 d 26 zs_W5 slices_W5 syms_W5 nextLv) (levels_W5[d]'hd) = true := by
  intro d hd
  match d with
  | 0 => exact l0 | 1 => exact l1 | 2 => exact l2 | 3 => exact l3 | 4 => exact l4
  | 5 => exact l5 | 6 => exact l6 | 7 => exact l7 | 8 => exact l8 | 9 => exact l9 | _ + 10 => omega
theorem w5_signed_lb : ¬ HasSignedOn 6 (maskN 6) tgt_W5 10 :=
  cert_sound 6 tgt_W5 10 26 zs_W5 bases6 slices_W5 syms_W5 levels_W5
    (by decide) (by decide)
    (by obtain ⟨z1,o1,hz1,ho1,_,_,hne⟩ := hasZeroAndOne_sound 6 (maskN 6) tgt_W5 (by decide); exact ⟨z1,o1,hz1,ho1,hne⟩)
    (allEssCheck_sound 6 tgt_W5 (by decide))
    (zsCheck_sound 6 tgt_W5 zs_W5 (by decide))
    bases6_ok w5_slices_ok (slicesSomeCheck_sound 26 slices_W5 (by decide)) w5_syms_ok rfl w5_levels_ok
    ⟨by decide,(btGet v0 0).getD ⟨[],[],[],[],[]⟩,rfl,by decide +kernel,by decide +kernel⟩
theorem evalW5_eq_tgtW5 : ∀ k : Fin 64,evalW5 (pt 6 k.val) = tgt_W5.testBit k.val := by
  decide
theorem w5_no_10_signed : ∀ (sgs : List SGate) (o : ℕ) (pol : Bool),
    SCleanL 6 sgs -> sgs.length ≤ 10 -> o < 6 + sgs.length ->
    ¬ ∀ y : Fin 6 -> Bool,xor ((sWiresFrom sgs (List.ofFn y)).getD o false) pol = evalW5 y := by
  intro sgs o pol hcl hlen ho hev
  apply w5_signed_lb
  refine ⟨sgs,o,pol,hcl,hlen,ho,fun k hk _ => ?_⟩
  have h1 := hev (pt 6 k)
  have h2 := evalW5_eq_tgtW5 ⟨k,hk⟩
  exact h1.trans h2
end PEqualNP.Outside.L_meta_10650_aux
theorem PEqualNP.Outside.L_meta_10650 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  PEqualNP.Outside.L_meta_10650_aux.reduce_G_to_W5 PEqualNP.Outside.L_meta_10650_aux.w5_no_10_signed

