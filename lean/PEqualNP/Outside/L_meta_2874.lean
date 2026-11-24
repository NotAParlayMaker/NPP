import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership

namespace PEqualNP.Outside.L_meta_2874_aux

-- A marked wire is an input or an OR of wires on the same side of the bipartition.
private def Layers (n m : ℕ) (C : Circuit) (S : Bool → Finset ℕ) : Prop :=
  (∀ t w, w ∈ S t → (w < n+m ∧ decide (n ≤ w) = t) ∨
    ∃ i < C.size, w = n+m+i ∧ (gateAt C i).op = .or ∧ ∀ u ∈ (gateAt C i).inputs, u ∈ S t) ∧
  ∀ i < C.size, (gateAt C i).op = .and →
    ∃ a b t, (gateAt C i).inputs = [a,b] ∧ a ∈ S t ∧ b ∈ S (!t)

private def wire {k : ℕ} (C : Circuit) (x : Fin k → Bool) (i : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD i false

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem runLength (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

private theorem inputWire {k : ℕ} (C : Circuit) (x : Fin k → Bool) (i : Fin k) :
    wire C x i = x i := by
  change (C.gates.foldl step (List.ofFn x)).getD i false = _
  have old (G : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
      (G.foldl step w).getD j false = w.getD j false := by
    induction G generalizing w with
    | nil => rfl
    | cons g G ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hj
  have hi : i.val < (List.ofFn x).length := by simp
  rw [old _ _ _ hi, List.getD_eq_getElem _ _ hi, List.getElem_ofFn]

private def addGate (k : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨op, [a,b]⟩], k+C.size⟩

private theorem addSize (k : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) :
    (addGate k C op a b).size = C.size + 1 := by
  simp [addGate, Circuit.size]

private theorem addOld {k : ℕ} (C : Circuit) (op : GateOp) (a b i : ℕ)
    (hi : i < k+C.size) (x : Fin k → Bool) : wire (addGate k C op a b) x i = wire C x i := by
  change ((C.gates ++ [Gate.mk op [a,b]]).foldl step (List.ofFn x)).getD i false = _
  rw [List.foldl_append]
  change ((C.gates.foldl step (List.ofFn x)) ++ [_]).getD i false = _
  exact List.getD_append _ _ _ _ (by simpa [runLength, Circuit.size] using hi)

private theorem addNew {k : ℕ} (C : Circuit) (op : GateOp) (a b : ℕ)
    (x : Fin k → Bool) :
    wire (addGate k C op a b) x (k+C.size) = op.eval [wire C x a, wire C x b] := by
  change ((C.gates ++ [Gate.mk op [a,b]]).foldl step (List.ofFn x)).getD (k+C.size) false = _
  rw [List.foldl_append]
  change ((C.gates.foldl step (List.ofFn x)) ++
    [op.eval [wire C x a, wire C x b]]).getD (k+C.size) false = _
  have len : (C.gates.foldl step (List.ofFn x)).length = k+C.size := by
    rw [runLength, List.length_ofFn]
    rfl
  rw [← len, List.getD_append_right _ _ _ _ (by omega), Nat.sub_self, List.getD_cons_zero]

private theorem atOld (k : ℕ) (C : Circuit) (op : GateOp) (a b j : ℕ) (hj : j < C.size) :
    gateAt (addGate k C op a b) j = gateAt C j :=
  List.getD_append _ _ _ _ hj

private theorem atNew (k : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) :
    gateAt (addGate k C op a b) C.size = ⟨op,[a,b]⟩ := by
  change (C.gates ++ [Gate.mk op [a,b]]).getD C.gates.length _ = _
  rw [List.getD_append_right _ _ _ _ (by omega), Nat.sub_self, List.getD_cons_zero]

private def mark (S : Bool → Finset ℕ) (label : Option Bool) (w : ℕ) (t : Bool) :
    Finset ℕ :=
  if label = some t then insert w (S t) else S t

private theorem markOld (S : Bool → Finset ℕ) (label : Option Bool) (w : ℕ) (t : Bool) :
    S t ⊆ mark S label w t := by
  intro u hu
  unfold mark
  split
  · exact Finset.mem_insert_of_mem hu
  · exact hu

private theorem markNew (S : Bool → Finset ℕ) (w : ℕ) (t : Bool) :
    w ∈ mark S (some t) w t := by simp [mark]

private theorem addLayers {n m : ℕ} {C : Circuit} {S : Bool → Finset ℕ}
    (hAO : IsAO2 (n+m) C) (hS : Layers n m C S)
    (op : GateOp) (a b : ℕ) (label : Option Bool)
    (ha : a < n+m+C.size) (hb : b < n+m+C.size)
    (ho : op = .and ∨ op = .or)
    (cross : op = .and → ∃ t, a ∈ S t ∧ b ∈ S (!t))
    (same : ∀ t, label = some t → op = .or ∧ a ∈ S t ∧ b ∈ S t) :
    IsAO2 (n+m) (addGate (n+m) C op a b) ∧
      Layers n m (addGate (n+m) C op a b) (mark S label (n+m+C.size)) := by
  let D := addGate (n+m) C op a b
  let T := mark S label (n+m+C.size)
  have hs : D.size = C.size+1 := addSize _ _ _ _ _
  have stable (j : ℕ) (hj : j < C.size) : gateAt D j = gateAt C j :=
    atOld _ _ _ _ _ _ hj
  have last : gateAt D C.size = ⟨op,[a,b]⟩ := atNew _ _ _ _ _
  have keep (t : Bool) : S t ⊆ T t := markOld _ _ _ _
  change IsAO2 (n+m) D ∧ Layers n m D T
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro g hg
    change g ∈ C.gates ++ [Gate.mk op [a,b]] at hg
    rcases List.mem_append.mp hg with h | h
    · exact hAO.1 g h
    · obtain rfl := List.mem_singleton.mp h
      exact ho
  · intro j hj i hi
    change j < D.size at hj
    by_cases hj' : j < C.size
    · rw [stable j hj'] at hi
      exact hAO.2.1 j hj' i hi
    · have he : j = C.size := by omega
      subst j
      rw [last] at hi
      rcases (show i = a ∨ i = b from by simpa using hi) with rfl | rfl
      · exact ha
      · exact hb
  · intro g hg
    change g ∈ C.gates ++ [Gate.mk op [a,b]] at hg
    rcases List.mem_append.mp hg with h | h
    · exact hAO.2.2 g h
    · obtain rfl := List.mem_singleton.mp h
      rfl
  · intro t w hw
    have old (hws : w ∈ S t) : (w < n+m ∧ decide (n ≤ w) = t) ∨
        ∃ i < D.size, w = n+m+i ∧ (gateAt D i).op = .or ∧
          ∀ u ∈ (gateAt D i).inputs, u ∈ T t := by
      rcases hS.1 t w hws with h | ⟨i, hi, he, hop, hm⟩
      · exact Or.inl h
      · exact Or.inr ⟨i, by omega, he, by rwa [stable i hi],
          fun u hu => keep t (hm u (by rwa [stable i hi] at hu))⟩
    change w ∈ mark S label (n+m+C.size) t at hw
    unfold mark at hw
    split at hw
    next hlabel =>
      rcases Finset.mem_insert.mp hw with rfl | hw
      · obtain ⟨hOp, hA, hB⟩ := same t hlabel
        refine Or.inr ⟨C.size, by omega, rfl, by simpa only [last] using hOp, ?_⟩
        intro u hu
        rw [last] at hu
        rcases (show u = a ∨ u = b from by simpa using hu) with rfl | rfl
        · exact keep t hA
        · exact keep t hB
      · exact old hw
    next => exact old hw
  · intro j hj hOp
    by_cases hj' : j < C.size
    · rw [stable j hj'] at hOp ⊢
      obtain ⟨a', b', t, hh, ha', hb'⟩ := hS.2 j hj' hOp
      exact ⟨a', b', t, hh, keep t ha', keep (!t) hb'⟩
    · have he : j = C.size := by omega
      subst j
      rw [last] at hOp ⊢
      obtain ⟨t, ha', hb'⟩ := cross hOp
      exact ⟨a,b,t,rfl,keep t ha',keep (!t) hb'⟩

private theorem andValue (a b : Bool) : GateOp.and.eval [a,b] = (a && b) := by
  cases a <;> cases b <;> rfl

private theorem orValue (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by
  cases a <;> cases b <;> rfl

private theorem andNeOr : GateOp.and ≠ GateOp.or := fun h => GateOp.noConfusion h

private theorem orNeAnd : GateOp.or ≠ GateOp.and := Ne.symm andNeOr

-- Start with a real leaf and use exactly one OR for every additional leaf.
private theorem orLeaves {n m : ℕ} (t : Bool) (L : List ℕ)
    (C : Circuit) (S : Bool → Finset ℕ) (a : ℕ)
    (hAO : IsAO2 (n+m) C) (hS : Layers n m C S)
    (ha : a < n+m+C.size) (hsa : a ∈ S t)
    (hL : ∀ i ∈ L, i < n+m+C.size ∧ i ∈ S t) :
    ∃ (D : Circuit) (T : Bool → Finset ℕ) (w : ℕ),
      IsAO2 (n+m) D ∧ Layers n m D T ∧ (∀ u, S u ⊆ T u) ∧
      D.size = C.size+L.length ∧ w < n+m+D.size ∧ w ∈ T t ∧
      (∀ (x : Fin (n+m) → Bool) i, i < n+m+C.size → wire D x i = wire C x i) ∧
      ∀ (x : Fin (n+m) → Bool), wire D x w = true ↔ wire C x a = true ∨ ∃ i ∈ L, wire C x i = true := by
  induction L generalizing C S a with
  | nil =>
    exact ⟨C,S,a,hAO,hS,fun _ => Finset.Subset.rfl,by simp,ha,hsa,fun _ _ _ => rfl,
      fun _ => by simp⟩
  | cons b L ih =>
    let C' := addGate (n+m) C .or a b
    let S' := mark S (some t) (n+m+C.size)
    have hb := hL b List.mem_cons_self
    obtain ⟨hAO', hS'⟩ := addLayers hAO hS .or a b (some t) ha hb.1 (Or.inr rfl)
      (fun h => (orNeAnd h).elim) (by
        intro u hu
        obtain rfl := Option.some.inj hu
        exact ⟨rfl,hsa,hb.2⟩)
    have hc' : C'.size = C.size + 1 := addSize _ _ _ _ _
    have hin (i : ℕ) (hi : i < n+m+C.size) : i < n+m+C'.size := by omega
    have hm (u : Bool) : S u ⊆ S' u := markOld _ _ _ _
    obtain ⟨D,T,w,hAOd,hSd,hkeep,hlen,hw,hwt,hstable,he⟩ :=
      ih C' S' (n+m+C.size) hAO' hS' (by omega) (markNew _ _ _)
        (fun i hi => let h := hL i (List.mem_cons_of_mem _ hi)
          ⟨hin i h.1, hm t h.2⟩)
    have hstable' (x : Fin (n+m) → Bool) (i : ℕ) (hi : i < n+m+C.size) :
        wire C' x i = wire C x i := addOld C .or a b i hi x
    refine ⟨D,T,w,hAOd,hSd,fun u => (hm u).trans (hkeep u),by simp [hlen,hc',Nat.add_assoc,Nat.add_comm],
      hw,hwt,fun x i hi => (hstable x i (hin i hi)).trans (hstable' x i hi),?_⟩
    intro x
    rw [he x, show wire C' x (n+m+C.size) = (wire C x a || wire C x b) from
      (addNew C .or a b x).trans (orValue _ _), Bool.or_eq_true]
    have hr : (∃ i ∈ L, wire C' x i = true) ↔ ∃ i ∈ L, wire C x i = true := by
      simp only [← exists_prop]
      constructor <;> rintro ⟨i,hi,h⟩ <;> refine ⟨i,hi,?_⟩
      · rwa [← hstable' x i (hL i (List.mem_cons_of_mem _ hi)).1]
      · rwa [hstable' x i (hL i (List.mem_cons_of_mem _ hi)).1]
    rw [hr]
    simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left, or_assoc]

private def MarksInput (n m : ℕ) (S : Bool → Finset ℕ) : Prop :=
  ∀ (i : Fin (n+m)), i.val ∈ S (decide (n ≤ i.val))

private theorem addStar {n m : ℕ} (t : Bool) (c a : Fin (n+m)) (L : List (Fin (n+m)))
    (C : Circuit) (S : Bool → Finset ℕ)
    (hAO : IsAO2 (n+m) C) (hS : Layers n m C S) (hm : MarksInput n m S)
    (hc : decide (n ≤ c.val) = !t) (ha : decide (n ≤ a.val) = t)
    (hL : ∀ i ∈ L, decide (n ≤ (i : ℕ)) = t) :
    ∃ (D : Circuit) (T : Bool → Finset ℕ),
      IsAO2 (n+m) D ∧ Layers n m D T ∧ MarksInput n m T ∧
      D.size = C.size+L.length+1 ∧ D.output < n+m+D.size ∧
      (∀ (x : Fin (n+m) → Bool) i, i < n+m+C.size → wire D x i = wire C x i) ∧
      ∀ (x : Fin (n+m) → Bool), circuitFun (n+m) D x = true ↔
        x c = true ∧ (x a = true ∨ ∃ i ∈ L, x i = true) := by
  have inBound (u : Fin (n+m)) : (u : ℕ) < n+m+C.size := by have := u.isLt; omega
  have marked (u : Fin (n+m)) (v : Bool) (h : decide (n ≤ u.val) = v) : u.val ∈ S v :=
    h ▸ hm u
  obtain ⟨D,T,w,hAOd,hSd,hkeep,hlen,hw,hT,hold,heval⟩ :=
    orLeaves t (L.map Fin.val) C S a hAO hS (inBound a) (marked a t ha) (by
      intro i hi
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hi
      exact ⟨inBound u,marked u t (hL u hu)⟩)
  let D' := addGate (n+m) D .and w c
  let T' := mark T none (n+m+D.size)
  have hcc : (c : ℕ) < n+m+D.size := by have := c.isLt; omega
  obtain ⟨hAO',hS'⟩ := addLayers hAOd hSd .and w c none hw hcc (Or.inl rfl)
    (fun _ => ⟨t,hT,hkeep (!t) (marked c (!t) hc)⟩) (by simp)
  have hlen' : D'.size = D.size+1 := addSize _ _ _ _ _
  have hroot : D'.output = n+m+D.size := rfl
  refine ⟨D',T',hAO',hS',fun i => markOld _ _ _ _ (hkeep _ (hm i)),by
    rw [hlen',hlen,List.length_map],by rw [hroot,hlen']; omega,?_,?_⟩
  · intro x i hi
    exact (addOld D .and w c i (by omega) x).trans (hold x i hi)
  · intro x
    change wire D' x D'.output = true ↔ _
    rw [hroot,addNew D .and w c x,andValue,Bool.and_eq_true,heval x,inputWire,inputWire]
    suffices (∃ i ∈ L.map Fin.val, wire C x i = true) ↔ ∃ i ∈ L, x i = true by
      rw [this, and_comm]
    constructor
    · rintro ⟨i, hi, hs⟩
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hi
      exact ⟨u,hu,(inputWire C x u) ▸ hs⟩
    · rintro ⟨u,hu,hs⟩
      exact ⟨u,List.mem_map_of_mem hu,(inputWire C x u).symm ▸ hs⟩

private theorem mergeOutput {n m : ℕ} (C D : Circuit) (S : Bool → Finset ℕ)
    (hAO : IsAO2 (n+m) D) (hS : Layers n m D S) (hm : MarksInput n m S)
    (hsize : C.size ≤ D.size) (hC : C.output < n+m+C.size)
    (hD : D.output < n+m+D.size)
    (preserve : ∀ (x : Fin (n+m) → Bool), wire D x C.output = wire C x C.output) :
    ∃ (F : Circuit) (T : Bool → Finset ℕ), IsAO2 (n+m) F ∧ Layers n m F T ∧
      MarksInput n m T ∧ F.size = D.size+1 ∧ F.output < n+m+F.size ∧
      ∀ x, circuitFun (n+m) F x = true ↔
        circuitFun (n+m) C x = true ∨ circuitFun (n+m) D x = true := by
  let F := addGate (n+m) D .or C.output D.output
  let T := mark S none (n+m+D.size)
  obtain ⟨hF,hT⟩ := addLayers hAO hS .or C.output D.output none (by omega) hD
    (Or.inr rfl) (fun h => (orNeAnd h).elim) (by simp)
  have hs : F.size = D.size + 1 := addSize _ _ _ _ _
  have hr : F.output = n+m+D.size := rfl
  refine ⟨F,T,hF,hT,fun i => markOld _ _ _ _ (hm i),hs,by rw [hr,hs]; omega,?_⟩
  intro x
  change wire F x F.output = true ↔
    wire C x C.output = true ∨ wire D x D.output = true
  rw [hr,addNew D .or C.output D.output x,orValue,preserve x,Bool.or_eq_true]

private def Touches {n m : ℕ} (d : Fin n ⊕ Fin m) (e : Fin n × Fin m) : Prop :=
  match d with
  | .inl p => e.1 = p
  | .inr l => e.2 = l

private def centerWire {n m : ℕ} (d : Fin n ⊕ Fin m) : Fin (n+m) :=
  match d with
  | .inl p => Fin.castAdd m p
  | .inr l => Fin.natAdd n l

private def otherWire {n m : ℕ} (d : Fin n ⊕ Fin m) (e : Fin n × Fin m) : Fin (n+m) :=
  match d with
  | .inl _ => Fin.natAdd n e.2
  | .inr _ => Fin.castAdd m e.1

private def leafSide {n m : ℕ} (d : Fin n ⊕ Fin m) : Bool :=
  match d with
  | .inl _ => true
  | .inr _ => false

private theorem centerSide {n m : ℕ} (d : Fin n ⊕ Fin m) :
    decide (n ≤ (centerWire d).val) = !leafSide d := by
  cases d with
  | inl p => simp [centerWire, leafSide, Nat.not_le.mpr p.isLt]
  | inr l => simp [centerWire, leafSide]

private theorem otherSide {n m : ℕ} (d : Fin n ⊕ Fin m) (e : Fin n × Fin m) :
    decide (n ≤ (otherWire d e).val) = leafSide d := by
  cases d with
  | inl p => simp [otherWire, leafSide]
  | inr l => simp [otherWire, leafSide, Nat.not_le.mpr e.1.isLt]

private def EdgeOn {n m : ℕ} (x : Fin (n+m) → Bool) (e : Fin n × Fin m) : Prop :=
  x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd n e.2) = true

private theorem pairOn {n m : ℕ} (d : Fin n ⊕ Fin m) (e : Fin n × Fin m)
    (h : Touches d e) (x : Fin (n+m) → Bool) :
    x (centerWire d) = true ∧ x (otherWire d e) = true ↔ EdgeOn x e := by
  cases d with
  | inl p =>
    change e.1 = p at h
    simp [centerWire, otherWire, EdgeOn, h]
  | inr l =>
    change e.2 = l at h
    simp [centerWire, otherWire, EdgeOn, h, and_comm]

private theorem hitSpec {n m : ℕ} (d : Fin n ⊕ Fin m) (e : Fin n × Fin m)
    (L : List (Fin n × Fin m)) (H : Finset (Fin n × Fin m)) (ht : H.toList = e :: L)
    (touch : ∀ f ∈ H, Touches d f) (x : Fin (n+m) → Bool) :
    (x (centerWire d) = true ∧
      (x (otherWire d e) = true ∨ ∃ i ∈ L.map (otherWire d), x i = true)) ↔
      ∃ f ∈ H, EdgeOn x f := by
  have mem (f : Fin n × Fin m) : f ∈ H ↔ f = e ∨ f ∈ L := by
    rw [← Finset.mem_toList, ht, List.mem_cons]
  constructor
  · rintro ⟨hc, h | ⟨w, hw, h⟩⟩
    · have he := (mem e).2 (Or.inl rfl)
      exact ⟨e,he,(pairOn d e (touch e he) x).1 ⟨hc,h⟩⟩
    · obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hw
      have hm := (mem f).2 (Or.inr hf)
      exact ⟨f,hm,(pairOn d f (touch f hm) x).1 ⟨hc,h⟩⟩
  · rintro ⟨f,hf,h⟩
    obtain ⟨hc,hf'⟩ := (pairOn d f (touch f hf) x).2 h
    refine ⟨hc,?_⟩
    rcases (mem f).1 hf with rfl | hm
    · exact Or.inl hf'
    · exact Or.inr ⟨otherWire d f,List.mem_map_of_mem hm,hf'⟩

private theorem emptyBuild (n m : ℕ) :
    ∃ (C : Circuit) (S : Bool → Finset ℕ),
      IsAO2 (n+m) C ∧ Layers n m C S ∧ MarksInput n m S ∧
      C.size = 0 ∧ ∀ (x : Fin (n+m) → Bool), circuitFun (n+m) C x = false := by
  let C : Circuit := ⟨[],n+m⟩
  let S (t : Bool) := (Finset.range (n+m)).filter fun i => decide (n ≤ i) = t
  refine ⟨C, S, ⟨by simp [AndOrOnly,C], by simp [ReadsBack,C], by simp [C]⟩, ⟨?_,?_⟩,
    ?_, rfl, ?_⟩
  · intro t w hw
    exact Or.inl (by simpa [S] using hw)
  · change ∀ i < 0, _
    simp
  · intro i
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.isLt,rfl⟩
  · intro x
    change (List.ofFn x).getD (n+m) false = false
    simp [List.getD]

set_option maxHeartbeats 3000000 in
private theorem compile {n m : ℕ} (L : List (Fin n ⊕ Fin m))
    (E : Finset (Fin n × Fin m))
    (cover : ∀ e ∈ E, ∃ d ∈ L, Touches d e) :
    ∃ (C : Circuit) (S : Bool → Finset ℕ),
      IsAO2 (n+m) C ∧ Layers n m C S ∧ MarksInput n m S ∧
      C.size ≤ E.card + L.length - 1 ∧
      (E.Nonempty → C.output < n+m+C.size) ∧
      ∀ x, circuitFun (n+m) C x = true ↔ ∃ f ∈ E, EdgeOn x f := by
  classical
  induction L generalizing E with
  | nil =>
    have hEmpty : E = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨d,hd,_⟩ := cover e he
      exact List.not_mem_nil hd
    subst E
    obtain ⟨C,S,hAO,hS,hm,hlen,hval⟩ := emptyBuild n m
    exact ⟨C,S,hAO,hS,hm,by simp [hlen],by simp,fun x => by simp [hval x]⟩
  | cons d L ih =>
    -- Assign each remaining incident edge to this center, then remove it from the recursion.
    let H := E.filter (Touches d)
    let R := E \ H
    have hHE : H ⊆ E := Finset.filter_subset _ _
    have hRE : R ⊆ E := Finset.sdiff_subset
    have hCard : R.card + H.card = E.card := Finset.card_sdiff_add_card_eq_card hHE
    have hCoverR : ∀ e ∈ R, ∃ d' ∈ L, Touches d' e := by
      intro e he
      obtain ⟨d',hd',hd'e⟩ := cover e (hRE he)
      rcases List.mem_cons.mp hd' with rfl | hd'
      · exact (Finset.mem_sdiff.mp he).2 (Finset.mem_filter.mpr ⟨hRE he,hd'e⟩) |>.elim
      · exact ⟨d',hd',hd'e⟩
    obtain ⟨C,S,hAO,hS,hm,hsize,hroot,heval⟩ := ih R hCoverR
    cases hH : H.toList with
    | nil =>
      have he : H = ∅ := by simpa using hH
      have hr : R = E := by simp [R,he]
      refine ⟨C,S,hAO,hS,hm,?_,?_,?_⟩
      · simp only [hr] at hsize
        simp only [List.length_cons]
        omega
      · rwa [hr] at hroot
      · simpa only [hr] using heval
    | cons e ls =>
      have hHcard : H.card = ls.length + 1 := by
        rw [← Finset.length_toList, hH, List.length_cons]
      let a := otherWire d e
      let leaves := ls.map (otherWire d)
      obtain ⟨D,T,hAOd,hSd,hmd,hsd,houtd,hpres,hvald⟩ :=
        addStar (leafSide d) (centerWire d) a leaves C S hAO hS hm
          (centerSide d) (otherSide d e) (by
            intro i hi
            obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hi
            exact otherSide d f)
      have hDcard : D.size = C.size + H.card := by
        simpa [leaves,hHcard,Nat.add_assoc] using hsd
      have hDEval (x : Fin (n+m) → Bool) :
          circuitFun (n+m) D x = true ↔ ∃ f ∈ H, EdgeOn x f :=
        (hvald x).trans (hitSpec d e ls H hH (fun f hf => (Finset.mem_filter.mp hf).2) x)
      by_cases hR : R.Nonempty
      · obtain ⟨F,U,hAOf,hSf,hmf,hsf,hof,hvalf⟩ :=
          mergeOutput C D T hAOd hSd hmd (by omega) (hroot hR) houtd
            (fun x => hpres x C.output (hroot hR))
        refine ⟨F,U,hAOf,hSf,hmf,?_,fun _ => hof,?_⟩
        · have hRpos := Finset.card_pos.mpr hR
          simp only [List.length_cons]
          omega
        · intro x
          rw [hvalf,heval,hDEval]
          constructor
          · rintro (⟨f,hf,h⟩ | ⟨f,hf,h⟩)
            · exact ⟨f,hRE hf,h⟩
            · exact ⟨f,hHE hf,h⟩
          · rintro ⟨f,hf,h⟩
            by_cases hf' : f ∈ H
            · exact Or.inr ⟨f,hf',h⟩
            · exact Or.inl ⟨f,Finset.mem_sdiff.mpr ⟨hf,hf'⟩,h⟩
      · have hEmpty := Finset.not_nonempty_iff_eq_empty.mp hR
        have hE : E = H := by
          apply Finset.Subset.antisymm _ hHE
          intro f hf
          by_contra h
          have : f ∈ R := Finset.mem_sdiff.mpr ⟨hf,h⟩
          simpa [hEmpty] using this
        refine ⟨D,T,hAOd,hSd,hmd,?_,fun _ => houtd,?_⟩
        · simp only [List.length_cons]
          omega
        · simpa only [hE] using hDEval

end PEqualNP.Outside.L_meta_2874_aux

open PEqualNP.Outside.L_meta_2874_aux

theorem PEqualNP.Outside.L_meta_2874 :
  ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)),
    (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) →
    ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : Bool → Finset ℕ),
      PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧
      x7.size ≤ x3.card + x4.card + x5.card - (1 : ℕ) ∧
      (∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x9 =
        Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2),
          (x10, x11) ∈ x3 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) ∧
      have x9 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x7;
      (∀ (x10 : Bool), ∀ x11 ∈ x8 x10, x11 < x1 + x2 ∧ Decidable.decide (x1 ≤ x11) = x10 ∨
        ∃ x13 < x7.size, x11 = x1 + x2 + x13 ∧ (x9 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        ∀ x14 ∈ (x9 x13).inputs, x14 ∈ x8 x10) ∧
      ∀ x10 < x7.size, (x9 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ∃ (x13 : ℕ) (x14 : ℕ) (x15 : Bool), (x9 x10).inputs = [x13, x14] ∧ x13 ∈ x8 x15 ∧ x14 ∈ x8 !x15 := by
  classical
  intro n m E A B h
  let L : List (Fin n ⊕ Fin m) := A.toList.map Sum.inl ++ B.toList.map Sum.inr
  have hCover : ∀ e ∈ E, ∃ d ∈ L, Touches d e := by
    intro e he
    rcases h e he with ha | hb
    · refine ⟨Sum.inl e.1,List.mem_append_left _ ?_,rfl⟩
      exact List.mem_map_of_mem (Finset.mem_toList.mpr ha)
    · refine ⟨Sum.inr e.2,List.mem_append_right _ ?_,rfl⟩
      exact List.mem_map_of_mem (Finset.mem_toList.mpr hb)
  obtain ⟨C,S,hAO,hS,_,hsize,_,hval⟩ := compile L E hCover
  refine ⟨C,S,hAO,?_,?_,hS⟩
  · simpa [L, Nat.add_assoc] using hsize
  · intro x
    rw [Bool.eq_iff_iff, hval x, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨p,l⟩, hmem, hp, hl⟩
      exact ⟨p,l,hmem,hp,hl⟩
    · rintro ⟨p,l,hmem,hp,hl⟩
      exact ⟨(p,l),hmem,hp,hl⟩
