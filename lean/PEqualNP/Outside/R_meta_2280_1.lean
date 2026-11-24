import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Each integer encodes a wire on the twenty-one minimal edges followed by
-- the thirty-seven maximal independent sets. A wire dominates another when
-- it preserves every correct row of the other wire. A gate with a dominating
-- predecessor signal costs no step. A new signal replaces all signals it dominates.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2200000 in
theorem PEqualNP.Outside.R_meta_2280_1
    (sampling : let pairs : List ℕ := [7,8,10,23,25,29,40,44,45,55,59,60,74,75,77,89,90,92,104,105,107]
    let test (x : Fin 14 → Bool) := pairs.any (fun e => x (Fin.ofNat 14 (e/16)) && x (Fin.ofNat 14 (e%16)))
    let rows : List ℕ := [129,257,1025,130,514,8194,260,4100,8196,136,2056,4104,1040,2064,8208,544,1056,4128,320,576,2112,127,244,314,432,541,660,792,1102,1220,1290,1548,2087,2212,2338,2565,3078,3716,4179,4304,4370,4625,5008,5186,6147,7426,8297,8416,8488,8713,9288,9992,10273,10656,12353,13504,14849,16256]
    ∀ i : Fin 58, let x := fun j : Fin 14 => (rows.getD i.val 0).testBit j.val
      ((test x=true ∧ ∀ j, x j=true → test (Function.update x j false)≠true) ∨
       (test x≠true ∧ ∀ j, x j=false → test (Function.update x j true)=true)) ∧
        (test x=true ↔ decide (i.val<21)=true))
    (incident : let dom := fun (a b : ℕ) => ∀ i : Fin 58, a.testBit i.val = decide (i.val<21) → b.testBit i.val = decide (i.val<21)
    let step := fun (s : List ℕ) (t : Bool × ℕ × ℕ) =>
      let v := if t.1 then t.2.1 &&& t.2.2 else t.2.1 ||| t.2.2
      if t.2.1 ∈ s ∧ t.2.2 ∈ s ∧ ¬ ∃ w ∈ s, dom v w then
        v :: s.filter (fun w => decide (¬dom w v)) else s
    ∀ trace : List (Bool × ℕ × ℕ), trace.length ≤ 25 →
      ∀ v ∈ trace.foldl step ([95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752,284526031944024591,0,288230376151711743] : List ℕ),
      ¬ ∀ i : Fin 58, v.testBit i.val = decide (i.val<21))
    (nonincident : let dom := fun (a b : ℕ) => ∀ i : Fin 58, a.testBit i.val = decide (i.val<21) → b.testBit i.val = decide (i.val<21)
    let step := fun (s : List ℕ) (t : Bool × ℕ × ℕ) =>
      let v := if t.1 then t.2.1 &&& t.2.2 else t.2.1 ||| t.2.2
      if t.2.1 ∈ s ∧ t.2.2 ∈ s ∧ ¬ ∃ w ∈ s, dom v w then
        v :: s.filter (fun w => decide (¬dom w v)) else s
    ∀ trace : List (Bool × ℕ × ℕ), trace.length ≤ 25 →
      ∀ v ∈ trace.foldl step ([95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752,241600541374316567,0,288230376151711743] : List ℕ),
      ¬ ∀ i : Fin 58, v.testBit i.val = decide (i.val<21))
    : have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : (Fin (14 : ℕ) → Bool) → Prop := fun (x3 : Fin (14 : ℕ) → Bool) => (x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.true → ¬x2 (Function.update x3 x4 Bool.false)) ∨ ¬x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.false → x2 (Function.update x3 x4 Bool.true); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin (14 : ℕ)), x5 = (7 : Fin (14 : ℕ)) ∨ x5 = (9 : Fin (14 : ℕ)) → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x8 : Fin (14 : ℕ) → Bool), x3 x8 → (x4.eval (List.ofFn x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [x8 (0 : Fin (14 : ℕ)), x8 x5]]) = Bool.true ↔ x2 x8)) → (26 : ℕ) ≤ x4.size := by

  let dom := fun (a b : ℕ) => ∀ i : Fin 58, a.testBit i.val = decide (i.val<21) → b.testBit i.val = decide (i.val<21)
  let step := fun (s : List ℕ) (t : Bool × ℕ × ℕ) =>
      let v := if t.1 then t.2.1 &&& t.2.2 else t.2.1 ||| t.2.2
      if t.2.1 ∈ s ∧ t.2.2 ∈ s ∧ ¬ ∃ w ∈ s, dom v w then
        v :: s.filter (fun w => decide (¬dom w v)) else s
  let table : List ℕ := [129,257,1025,130,514,8194,260,4100,8196,136,2056,4104,1040,2064,8208,544,1056,4128,320,576,2112,127,244,314,432,541,660,792,1102,1220,1290,1548,2087,2212,2338,2565,3078,3716,4179,4304,4370,4625,5008,5186,6147,7426,8297,8416,8488,8713,9288,9992,10273,10656,12353,13504,14849,16256]
  let signals : List ℕ := [95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752]
  let ones : ℕ := 288230376151711743
  let edges : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
  let hit (x : Fin 14 → Bool) := ∃ i j : Fin 14, (i.val,j.val)∈edges ∧ x i=true ∧ x j=true
  let boundary (x : Fin 14 → Bool) :=
    (hit x ∧ ∀ i, x i=true → ¬hit (Function.update x i false)) ∨
    (¬hit x ∧ ∀ i, x i=false → hit (Function.update x i true))
  let row (i : Fin 58) (j : Fin 14) := (table.getD i.val 0).testBit j.val
  let want (i : Fin 58) := decide (i.val<21)
  let test (x : Fin 14 → Bool) := edges.any (fun e => x (Fin.ofNat 14 e.1) && x (Fin.ofNat 14 e.2))
  have rangeE (e : ℕ × ℕ) (he : e∈edges) : e.1<14 ∧ e.2<14 := by
    simp only [edges,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst e <;> decide
  have hit_test (x : Fin 14 → Bool) : hit x ↔ test x=true := by
    constructor
    · rintro ⟨i,j,mem,a,b⟩
      apply List.any_eq_true.mpr
      refine ⟨(i.val,j.val),mem,?_⟩
      have fi (k : Fin 14) : Fin.ofNat 14 k.val=k := Fin.ext (Nat.mod_eq_of_lt k.isLt)
      simp [fi,a,b]
    · intro h
      obtain ⟨⟨a,b⟩,mem,on⟩ := List.any_eq_true.mp h
      obtain ⟨ha,hb⟩ := rangeE _ mem
      change (x (Fin.ofNat 14 a) && x (Fin.ofNat 14 b))=true at on
      simp only [Bool.and_eq_true] at on
      refine ⟨Fin.ofNat 14 a,Fin.ofNat 14 b,?_,on⟩
      simpa [Fin.ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using mem
  have rows (i : Fin 58) : boundary (row i) ∧ (hit (row i) ↔ want i=true) := by
    unfold boundary
    simp only [hit_test]
    exact sampling i
  have samples : ∀ (i : Fin 58) (j : Fin 14), (signals.getD j.val 0).testBit i.val=row i j := by decide
  have allBits : ∀ i : Fin 58, ones.testBit i.val=true := by decide
  let combine (a : Bool) (p q : ℕ) := if a then p &&& q else p ||| q
  have refl (u : ℕ) : dom u u := fun _ h => h
  have trans {a b c : ℕ} (h : dom a b) (k : dom b c) : dom a c := fun i v => k i (h i v)
  have truth : ∀ (op target a b c d : Bool),
      (a=target → c=target) → (b=target → d=target) →
      (if op then a && b else a || b) = target → (if op then c && d else c || d) = target := by decide
  have stronger {a b c d : ℕ} (op : Bool) (ac : dom a c) (bd : dom b d) :
      dom (combine op a b) (combine op c d) := by
    intro i
    have h := truth op (decide (i.val<21)) _ _ _ _ (ac i) (bd i)
    cases op <;> simpa only [combine,Bool.false_eq_true,ite_true,ite_false,Nat.testBit_and,Nat.testBit_or] using h
  have evalA (l : List Bool) : GateOp.and.eval l=l.all id := rfl
  have evalO (l : List Bool) : GateOp.or.eval l=l.any id := rfl
  let isAnd (g : Gate) := g.op.eval []
  let pin (g : Gate) (w : List ℕ) (k : ℕ) := if k<g.inputs.length then w.getD (g.inputs.getD k 0) 0
    else if isAnd g then ones else 0
  let gate (g : Gate) (w : List ℕ) := combine (isAnd g) (pin g w 0) (pin g w 1)
  let run (gs : List Gate) (w : List ℕ) := gs.foldl (fun u g => u++[gate g u]) w
  let good (g : Gate) := g.op∈({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2
  let actual (gs : List Gate) (v : List Bool) := gs.foldl
    (fun u g => u++[g.op.eval (g.inputs.map fun j => u.getD j false)]) v
  have read (w : List ℕ) (i : Fin 58) (j : ℕ) :
      (w.map (fun v => v.testBit i.val)).getD j false = (w.getD j 0).testBit i.val := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases w[j]? <;> simp
  have gateBit (g : Gate) (w : List ℕ) (i : Fin 58) (ok : good g) :
      (gate g w).testBit i.val = g.op.eval (g.inputs.map (fun j => (w.getD j 0).testBit i.val)) := by
    obtain ⟨o,ins⟩ := g
    obtain ⟨hop,arity⟩ := ok
    change o∈({GateOp.and,GateOp.or} : Set GateOp) at hop
    change ins.length≤2 at arity
    rcases hop with e|e <;> obtain rfl := e
    all_goals
      rcases ins with _|⟨a,_|⟨b,_|⟨c,tail⟩⟩⟩ <;>
        simp_all [gate,pin,isAnd,combine,evalA,evalO,Nat.testBit_and,Nat.testBit_or]
  have runBit (gs : List Gate) (ok : ∀ g∈gs, good g) (w : List ℕ) (i : Fin 58) :
      (run gs w).map (fun v => v.testBit i.val) = actual gs (w.map fun v => v.testBit i.val) := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (run gs (w++[gate g w])).map _ = actual gs ((w.map _)++[_])
      rw [ih (fun a h => ok a (List.mem_cons_of_mem _ h))]
      simp only [List.map_append,List.map_singleton,gateBit _ _ _ (ok _ List.mem_cons_self),read]
  let covered (w s : List ℕ) := ∀ u∈ones :: 0 :: w, ∃ v∈s, dom u v
  have readMem (w : List ℕ) (j : ℕ) : w.getD j 0 ∈ ones::0::w := by
    by_cases valid : j<w.length
    · rw [List.getD_eq_getElem _ _ valid]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.getElem_mem valid))
    · rw [List.getD_eq_default _ _ (by omega)]; simp
  have rawPin (g : Gate) (w : List ℕ) (k : ℕ) : pin g w k ∈ ones::0::w := by
    dsimp only [pin]
    split
    · exact readMem w _
    · split <;> simp
  have simulation (gs : List Gate) (w s : List ℕ) (hs : covered w s) :
      ∃ trace : List (Bool × ℕ × ℕ), trace.length ≤ gs.length ∧
        covered (run gs w) (trace.foldl step s) := by
    induction gs generalizing w s with
    | nil => exact ⟨[],le_rfl,hs⟩
    | cons g gs ih =>
      obtain ⟨a,ha,ea⟩ := hs _ (rawPin g w 0)
      obtain ⟨b,hb,eb⟩ := hs _ (rawPin g w 1)
      let op := isAnd g
      let v := combine op a b
      have improved : dom (gate g w) v := stronger op ea eb
      by_cases old : ∃ d∈s, dom v d
      · obtain ⟨d,hd,better⟩ := old
        have next : covered (w++[gate g w]) s := by
          intro u hu
          have alt : u∈ones::0::w ∨ u=gate g w := by
            simp only [List.mem_cons,List.mem_append,List.mem_singleton] at hu ⊢
            tauto
          rcases alt with gone|rfl
          · exact hs _ gone
          · exact ⟨d,hd,trans improved better⟩
        obtain ⟨rest,small,done⟩ := ih _ _ next
        exact ⟨rest,by simp; omega,done⟩
      · let t : Bool × ℕ × ℕ := (op,a,b)
        let n := v :: s.filter (fun z => decide (¬dom z v))
        have expand : step s t = n := by
          have guard : a∈s ∧ b∈s ∧ ¬∃ z∈s, dom v z := ⟨ha,hb,old⟩
          dsimp only [step,t]
          rw [ite_eq_left guard]
        have keep {u} (hu : u∈s) : ∃ z∈n, dom u z := by
          by_cases e : dom u v
          · exact ⟨v,List.mem_cons_self,e⟩
          · exact ⟨u,List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hu,by simpa using e⟩),refl _⟩
        have next : covered (w++[gate g w]) n := by
          intro u hu
          have alt : u∈ones::0::w ∨ u=gate g w := by
            simp only [List.mem_cons,List.mem_append,List.mem_singleton] at hu ⊢
            tauto
          rcases alt with gone|rfl
          · obtain ⟨z,hz,uz⟩ := hs _ gone
            obtain ⟨e,he,ze⟩ := keep hz
            exact ⟨e,he,trans uz ze⟩
          · exact ⟨v,List.mem_cons_self,improved⟩
        obtain ⟨rest,small,done⟩ := ih _ _ next
        refine ⟨t::rest,by simpa using small,?_⟩
        change covered (run gs (w++[gate g w])) (rest.foldl step (step s t))
        rw [expand]; exact done
  change ∀ (C : Circuit) (j : Fin 14), j=7 ∨ j=9 → Monotone2 C →
    (∀ x : Fin 14 → Bool, boundary x →
      (C.eval (List.ofFn x ++ [GateOp.or.eval [x 0,x j]])=true ↔ hit x)) → 26≤C.size
  intro C j choices legal correct
  by_contra low
  have cap : C.size ≤ 25 := by omega
  let added := signals.getD 0 0 ||| signals.getD j.val 0
  let w := signals ++ [added]
  let s := w ++ [0,ones]
  have initial : covered w s := by
    intro u hu
    refine ⟨u,?_,refl u⟩
    simp only [s,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    tauto
  obtain ⟨trace,ht,final⟩ := simulation C.gates w s initial
  have baseMap : ∀ i : Fin 58, signals.map (fun u => u.testBit i.val)=List.ofFn (row i) := by decide
  have bits (i : Fin 58) : w.map (fun u => u.testBit i.val) =
      List.ofFn (row i) ++ [GateOp.or.eval [row i 0,row i j]] := by
    simp only [w,List.map_append,baseMap,List.map_singleton,added,Nat.testBit_or]
    have h0 : (signals.getD 0 0).testBit i.val = row i 0 := samples i 0
    rw [h0,samples i j]
    change _ ++ [_] = _ ++ [row i 0 || (row i j || false)]
    simp
  let result := (run C.gates w).getD C.output 0
  have produces (i : Fin 58) : result.testBit i.val = want i := by
    change ((run C.gates w).getD C.output 0).testBit i.val = _
    rw [←read,runBit _ legal,bits]
    exact Bool.eq_iff_iff.mpr ((correct (row i) (rows i).1).trans (rows i).2)
  have seen : result ∈ ones :: 0 :: run C.gates w := readMem _ _
  obtain ⟨v,mem,better⟩ := final result seen
  have solves (i : Fin 58) : v.testBit i.val = want i := better i (produces i)
  have short := ht.trans cap
  rcases choices with rfl|rfl
  · have initEq : s = ([95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752,284526031944024591,0,288230376151711743] : List ℕ) := by decide
    rw [initEq] at mem
    exact incident trace short v mem solves
  · have initEq : s = ([95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752,241600541374316567,0,288230376151711743] : List ℕ) := by decide
    rw [initEq] at mem
    exact nonincident trace short v mem solves
