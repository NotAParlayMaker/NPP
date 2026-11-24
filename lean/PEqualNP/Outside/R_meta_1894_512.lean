import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The clean-circuit premise follows from the checked C4-free edge counting theorem.
-- A minimum-AND counterexample has every conjunction active on an edge.
-- A conjunction that reads a vertex directly cannot be active on that singleton.
set_option maxRecDepth 8000 in
set_option maxHeartbeats 16000000 in
theorem PEqualNP.Outside.R_meta_1894_512
    (dirty : ∀ C : Circuit, (Monotone2 C ∧ C.size≤124 ∧ (∀ z : Fin 42 → Bool, C.eval (List.ofFn z)=true ↔ (∃ a b : Fin 42, (a.val<21 ∧ 21≤b.val ∧ (b.val+21-a.val)%21∈[0,5,7,17,20]) ∧ z a=true ∧ z b=true))) →
      ∃ z : Fin 42 → Bool, ¬ (∃ a b : Fin 42, (a.val<21 ∧ 21≤b.val ∧ (b.val+21-a.val)%21∈[0,5,7,17,20]) ∧ z a=true ∧ z b=true) ∧ (∃ k g, C.gates[k]?=some g ∧ g.op=.and ∧ (C.wires (List.ofFn (z))).getD (42+k) false=true))
    (side : ∀ C : Circuit, Monotone2 C → C.size≤124 →
      (∀ pre post (g : Gate), C.gates=pre++g::post → g.op=.and →
       (∃ a b : Fin 42, decide ((a.val<21 ∧ 21≤b.val ∧ (b.val+21-a.val)%21∈[0,5,7,17,20]) ∨ (b.val<21 ∧ 21≤a.val ∧ (a.val+21-b.val)%21∈[0,5,7,17,20]))=true ∧
         g.op.eval (g.inputs.map fun i=>(Circuit.wires ⟨pre,0⟩ (List.ofFn (fun j : Fin 42 => decide (j=a ∨ j=b)))).getD i false) = true) ∧
       ∀ a : Fin 42, a.val∈g.inputs → g.op.eval (g.inputs.map fun i=>(Circuit.wires ⟨pre,0⟩ (List.ofFn (fun j : Fin 42 => decide (j=a)))).getD i false) = false) →
      (∃ k g, C.gates[k]?=some g ∧ g.op=.and ∧ (C.wires (List.ofFn (fun j : Fin 42 => decide (j=0 ∨ j=1)))).getD (42+k) false=true) →
      ∃ z : Fin 42 → Bool, ¬ (C.eval (List.ofFn z)=true ↔ (∃ a b : Fin 42, (a.val<21 ∧ 21≤b.val ∧ (b.val+21-a.val)%21∈[0,5,7,17,20]) ∧ z a=true ∧ z b=true)))
    (crossing : ∀ C : Circuit, Monotone2 C → C.size≤124 →
      (∀ pre post (g : Gate), C.gates=pre++g::post → g.op=.and →
       (∃ a b : Fin 42, decide ((a.val<21 ∧ 21≤b.val ∧ (b.val+21-a.val)%21∈[0,5,7,17,20]) ∨ (b.val<21 ∧ 21≤a.val ∧ (a.val+21-b.val)%21∈[0,5,7,17,20]))=true ∧
         g.op.eval (g.inputs.map fun i=>(Circuit.wires ⟨pre,0⟩ (List.ofFn (fun j : Fin 42 => decide (j=a ∨ j=b)))).getD i false) = true) ∧
       ∀ a : Fin 42, a.val∈g.inputs → g.op.eval (g.inputs.map fun i=>(Circuit.wires ⟨pre,0⟩ (List.ofFn (fun j : Fin 42 => decide (j=a)))).getD i false) = false) →
      (∃ k g, C.gates[k]?=some g ∧ g.op=.and ∧ (C.wires (List.ofFn (fun j : Fin 42 => decide (j=0 ∨ j=22)))).getD (42+k) false=true) →
      ∃ z : Fin 42 → Bool, ¬ (C.eval (List.ofFn z)=true ↔ (∃ a b : Fin 42, (a.val<21 ∧ 21≤b.val ∧ (b.val+21-a.val)%21∈[0,5,7,17,20]) ∧ z a=true ∧ z b=true))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → (∃ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x4]? = Option.some x5 ∧ x5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x6 : Fin (42 : ℕ)) => Decidable.decide (↑x6 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]))).getD ((42 : ℕ) + x4) Bool.false = Bool.true) → ∃ (x5 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), (↑x6 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x7 ∧ (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) := by
  let awake (C : Circuit) (x : Fin 42 → Bool) : Prop :=
    ∃ k g, C.gates[k]? = some g ∧ g.op = .and ∧ (C.wires (List.ofFn x)).getD (42+k) false=true
  let pairInput (p : Fin 42 × Fin 42) (i : Fin 42) := decide (i=p.1 ∨ i=p.2)

  let values (l : List Gate) (z : Fin 42 → Bool) := (Circuit.mk l 0).wires (List.ofFn z)
  let evaluate (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
  have prefix_nil (z) : values [] z = List.ofFn z := rfl
  have prefix_snoc (gs : List Gate) (g : Gate) (z : Fin 42 → Bool) :
      values (gs++[g]) z = values gs z ++ [evaluate g (values gs z)] := by
    change ((gs++[g]).foldl (fun v o => v++[evaluate o v]) (List.ofFn z))=_
    rw [List.foldl_append]
    rfl
  have prefix_len (gs : List Gate) (z) : (values gs z).length=42+gs.length := by
    induction gs using List.reverseRecOn with
    | nil => simp [prefix_nil]
    | append_singleton gs g ih => simp [prefix_snoc,ih,Nat.add_assoc]

  have old_wires (gs tail : List Gate) (z : Fin 42 → Bool) {i} (hi : i<42+gs.length) :
      (values (gs++tail) z).getD i false = (values gs z).getD i false := by
    induction tail using List.reverseRecOn with
    | nil => simp
    | append_singleton a g ih =>
      rw [←List.append_assoc, prefix_snoc, List.getD_append _ _ _ _ (by rw [prefix_len]; simp; omega), ih]

  have raised (gs tail : List Gate) (g : Gate) (z : Fin 42 → Bool) (hop : g.op=.and)
      (hv : evaluate g (values gs z)=true) : awake ⟨gs++g::tail,0⟩ z := by
    refine ⟨gs.length,g,by simp,hop,?_⟩
    change (values (gs++g::tail) z).getD _ _=_
    have eq : gs++g::tail=(gs++[g])++tail := by simp
    rw [eq, old_wires (gs++[g]) tail z (by simp),prefix_snoc]
    simpa only [←prefix_len gs z,List.getD_eq_getElem?_getD,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self,List.getElem?_cons_zero,Option.getD_some] using hv


  have dirty_pair (C : Circuit) (hm : Monotone2 C) (s : Fin 42 → Bool)
      (pairs : List (Fin 42 × Fin 42)) (inhab : ∃ p,p∈pairs)
      (cover : ∀ a b, s a=true → s b=true → ∃ p∈pairs, (a=p.1 ∨ a=p.2) ∧ (b=p.1 ∨ b=p.2))
      (hit : awake C s) : ∃ p∈pairs, awake C (pairInput p) := by
    by_contra! no
    let L := C.gates
    have rep (gs : List Gate) (pre : gs <+: L) :
        (∀ j, (values gs s).getD j false=true →
          ∃ a, s a=true ∧ ∀ p∈pairs, (a=p.1 ∨ a=p.2) → (values gs (pairInput p)).getD j false=true) ∧
        ¬ awake (Circuit.mk gs 0) s := by
      induction gs using List.reverseRecOn with
      | nil =>
        constructor
        · intro j hj
          have lt : j<42 := by
            by_contra! big
            rw [prefix_nil,List.getD_eq_default _ _ (by simp;omega)] at hj
            contradiction
          let a : Fin 42 := ⟨j,lt⟩
          have val (z : Fin 42 → Bool) : (values [] z).getD j false=z a := by
            rw [prefix_nil,List.getD_eq_getElem _ _ (by simpa using lt),List.getElem_ofFn]
          refine ⟨a,(val s).symm.trans hj,fun p _ ha => ?_⟩
          rw [val]; exact decide_eq_true ha
        · rintro ⟨k,g,hg,_,_⟩
          simp at hg
      | append_singleton gs g ih =>
        obtain ⟨tail,et⟩ := pre
        have et' : L=gs++g::tail := by simpa [List.append_assoc] using et.symm
        have prior : gs <+: L := ⟨g::tail,et'.symm⟩
        obtain ⟨rh,quiet⟩ := ih prior
        have legal := hm g (by change g∈L; rw [et']; simp)
        have compute (z : Fin 42 → Bool) : (values (gs++[g]) z).getD (42+gs.length) false =
            evaluate g (values gs z) := by
          rw [prefix_snoc,←prefix_len gs z]
          simp
        have cannot (ho : g.op=.and) : evaluate g (values gs s) ≠ true := by
          intro on
          let inputs := g.inputs
          have hall : ∀ j∈g.inputs, (values gs s).getD j false=true := by
            unfold evaluate at on
            rw [ho] at on
            change (g.inputs.map fun i => (values gs s).getD i false).all id = true at on
            intro j hj; exact List.all_eq_true.mp on _ (List.mem_map_of_mem hj)
          have force : ∃ p∈pairs, ∀ j∈g.inputs, (values gs (pairInput p)).getD j false=true := by
            have hl := legal.2
            cases hi : g.inputs with
            | nil =>
              obtain ⟨p,hp⟩ := inhab
              exact ⟨p,hp,by simp⟩
            | cons a as =>
              have haf := hall a (by simp [hi])
              obtain ⟨x,hx,fx⟩ := rh a haf
              cases as with
              | nil =>
                obtain ⟨p,hp,hp',_⟩ := cover x x hx hx
                exact ⟨p,hp,by simpa using fx p hp hp'⟩
              | cons b bs =>
                have hb := hall b (by simp [hi])
                obtain ⟨y,hy,fy⟩ := rh b hb
                obtain ⟨p,hp,hpx,hpy⟩ := cover x y hx hy
                have nil : bs=[] := List.length_eq_zero_iff.mp (by have hh : (a::b::bs).length ≤ 2 := hi ▸ hl; simpa using hh)
                subst bs
                exact ⟨p,hp,by simpa using And.intro (fx p hp hpx) (fy p hp hpy)⟩
          obtain ⟨p,hp,pvals⟩ := force
          have hon : evaluate g (values gs (pairInput p))=true := by
            unfold evaluate; rw [ho]
            change (g.inputs.map _).all id=true
            apply List.all_eq_true.mpr
            intro x hx
            obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
            exact pvals j hj
          have hbad := raised gs tail g (pairInput p) ho hon
          apply no p hp
          rcases C with ⟨cl,co⟩
          change cl=gs++g::tail at et'
          subst cl
          exact hbad
        constructor
        · intro j hj
          by_cases lt : j<42+gs.length
          · have inherit (z : Fin 42 → Bool) := old_wires gs [g] z lt
            rw [inherit] at hj
            obtain ⟨x,hx,fx⟩ := rh j hj
            exact ⟨x,hx,fun p hp hxp => (inherit _).trans (fx p hp hxp)⟩
          have eq : j=42+gs.length := by
            by_contra neq
            rw [List.getD_eq_default _ _ (by rw [prefix_len]; simp;omega)] at hj
            contradiction
          subst j
          rw [compute] at hj
          rcases (show g.op=.and ∨ g.op=.or from legal.1) with ho | ho
          · exact (cannot ho hj).elim
          unfold evaluate at hj; rw [ho] at hj
          change (g.inputs.map _).any id=true at hj
          obtain ⟨v,hv,hon⟩ := List.any_eq_true.mp hj
          obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hv
          obtain ⟨x,hx,fx⟩ := rh i hon
          refine ⟨x,hx,fun p hp hxp => ?_⟩
          rw [compute]; unfold evaluate; rw [ho]
          change (g.inputs.map _).any id=true
          exact List.any_eq_true.mpr ⟨_,List.mem_map_of_mem hi,fx p hp hxp⟩
        · rintro ⟨k,o,hk,ho,hv⟩
          by_cases lt : k<gs.length
          · apply quiet
            refine ⟨k,o,?_,ho,?_⟩
            · simpa only [List.getElem?_append_left lt] using hk
            · change (values (gs++[g]) s).getD (42+k) false=true at hv
              rw [old_wires gs [g] s (by omega)] at hv
              exact hv
          have eq : k=gs.length := by
            change (gs++[g])[k]?=some o at hk
            obtain ⟨hlen,_⟩ := List.getElem?_eq_some_iff.mp hk
            simp at hlen
            omega
          subst k
          have og : g=o := by simpa using hk
          subst o
          exact cannot ho ((compute s).symm.trans hv)
    exact (rep L ⟨[],by simp⟩).2 hit
  let wire (f : Fin 42 → Fin 42) (i : Nat) := if h:i<42 then (f ⟨i,h⟩).val else i
  let move (f : Fin 42 → Fin 42) (g : Gate) : Gate := ⟨g.op,g.inputs.map (wire f)⟩
  let renamed (f : Fin 42 → Fin 42) (C : Circuit) : Circuit := ⟨C.gates.map (move f),wire f C.output⟩

  have moved_values (f : Fin 42 → Fin 42) (gs : List Gate) (z : Fin 42 → Bool) (i : Nat) :
      (values (gs.map (move f)) z).getD (wire f i) false =
      (values gs (fun j=>z (f j))).getD i false := by
    induction gs using List.reverseRecOn generalizing i with
    | nil =>
      simp only [List.map_nil,prefix_nil]
      by_cases h:i<42
      · have h' := (f ⟨i,h⟩).isLt
        simp only [wire,dite_eq_left h]
        rw [List.getD_eq_getElem _ _ (by simp),List.getD_eq_getElem _ _ (by simpa using h)]
        simp only [List.getElem_ofFn]
      · simp only [wire,dite_eq_right h]
        rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]
    | append_singleton gs g ih =>
      simp only [List.map_append,List.map_singleton]
      by_cases h:i<42+gs.length
      · have hi : wire f i < 42+(gs.map (move f)).length := by
          simp only [wire,List.length_map]; split <;> rename_i hx
          · have := (f ⟨i,hx⟩).isLt; omega
          · exact h
        rw [old_wires _ [move f g] _ hi,old_wires gs [g] _ h,ih]
      · have idw : wire f i=i := dite_eq_right (by omega)
        rw [idw]
        by_cases e:i=42+gs.length
        · subst i
          rw [prefix_snoc,prefix_snoc]
          have last (w : List Bool) (b : Bool) : (w++[b]).getD w.length false=b := by simp
          have lp := prefix_len (gs.map (move f)) z
          simp only [List.length_map] at lp
          conv_lhs => arg 2; rw [←lp]
          conv_rhs => arg 2; rw [←prefix_len gs (fun j=>z (f j))]
          rw [last,last]
          unfold evaluate
          change g.op.eval ((g.inputs.map (wire f)).map _) = g.op.eval _
          rw [List.map_map]
          apply congrArg g.op.eval
          apply List.map_congr_left
          intro j _; exact ih j
        · rw [List.getD_eq_default _ _ (by rw [prefix_len]; simp;omega),
              List.getD_eq_default _ _ (by rw [prefix_len];simp;omega)]

  have renamed_eval (f : Fin 42 → Fin 42) (C : Circuit) (z : Fin 42 → Bool) :
      (renamed f C).eval (List.ofFn z)=C.eval (List.ofFn fun i=>z (f i)) := moved_values f C.gates z C.output

  have renamed_mono (f : Fin 42 → Fin 42) (C : Circuit) (hm : Monotone2 C) : Monotone2 (renamed f C) := by
    intro o ho
    change o∈C.gates.map (move f) at ho
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp ho
    simpa [move] using hm g hg

  have renamed_awake (f : Fin 42 → Fin 42) (C : Circuit) (z : Fin 42 → Bool)
      (h : awake C (fun i=>z (f i))) : awake (renamed f C) z := by
    obtain ⟨k,g,hg,ho,on⟩ := h
    refine ⟨k,move f g,?_,ho,?_⟩
    · change (C.gates.map (move f))[k]?=some (move f g)
      rw [List.getElem?_map,hg];rfl
    · have wf : wire f (42+k)=42+k := dite_eq_right (by omega)
      have eq := moved_values f C.gates z (42+k)
      rw [wf] at eq
      exact eq.trans on
  let incid (a b : Fin 42) := a.val<21 ∧ 21≤b.val ∧ (b.val+21-a.val)%21∈[0,5,7,17,20]
  let edge (a b : Fin 42) : Bool := decide (a.val<21 ∧ 21≤b.val ∧ (b.val+21-a.val)%21∈[0,5,7,17,20] ∨ b.val<21 ∧ 21≤a.val ∧ (a.val+21-b.val)%21∈[0,5,7,17,20])
  let present (z : Fin 42 → Bool) := ∃ a b, incid a b ∧ z a=true ∧ z b=true
  have symm_present (z : Fin 42 → Bool) : present z ↔ ∃ a b, edge a b=true ∧ z a=true ∧ z b=true := by
    constructor
    · rintro ⟨a,b,hi,ha,hb⟩
      exact ⟨a,b,decide_eq_true (Or.inl hi),ha,hb⟩
    · rintro ⟨a,b,h,ha,hb⟩
      rcases of_decide_eq_true h with ab | ba
      · exact ⟨a,b,ab,ha,hb⟩
      · exact ⟨b,a,ba,hb,ha⟩

  let generators : List Nat := [0x569a279a59238a181f79d71b69961758051349140f38d30b289207185103081,0x420c41461c824a2cc34e3d04524d40165d865a6dc75e7e08628e49669e8a55,0x6a25a95e58df85ea199dc6e681891d54644f0d024e14d09448b1ca3044c8040,0x9a48697e589d8166688da6d57979d870a40d0cb44830f1543891811024931c0]
  let action (k : Fin 4) (i : Fin 42) : Fin 42 :=
    Fin.ofNat 42 (((generators.getD k.val 0) >>> (6*i.val)) &&& 63)
  let rowCodes : List Nat := [
    0x1206000e11130f0b070f0e0a0015000a0f0b000004111b1611141b1618170a1f140b07130d11170000,
    0x1711001510111415111116150017001515150d000015181a15111611161a12181014111711151b0d0000,
    0xc00170f10131416151a1600140017131311000016141418151115171b18170f10151b16131b11000d17,
    0x14140e1612181716120013001716171500001a09101410171a1019161a140e121e1815151200131b11,
    0x1311111318171515190016001617151600001a0d00130c14170d1815151111161817151316001218150d,
    0x1010141714181419001300171a19180000181100110813181117161b151514171b19141b001615131113,
    0xe12171214121a001600191716160000141300150e0c17161216161b19121216171216001b1315161707,
    0x161714131418001b001a14141800001314001417151b18141b17171717181913141800161715181b110b,
    0x10101213170014001a11131400001b1300101a181116101a171518181719141314001b1218171c141414,
    0xc1016140010001b10171200001914000c1415160d0c1418161514151b101e10001414171b181210101e,
    0xf1712000f00160e131300001713000b121216130a121715161112180e180f001013131514160e0f1a0a,
    0x1414001200161a15150000171a0015121b16160d111b1818151616191519000f1d141912141114171217,
    0x1000150017191b1a0000191800171517171b111512171519171b1b15190019181019191215111a191b1a,
    0x18001616181a00001a160018181b17161519150d19161a1a151b1c001a150e1b17171a1515161b1615,
    0x17001617141b000017150017141715171419171100171b1b19151b001f151a1b141b1718181519171119,
    0x1417121800001616001012181318131a141700121414181618001a1819171214181716161810151414,
    0x1014161400001515000d15161a171517121500110013141514001b15151b161115151716140d18111111,
    0x131710000019140011161a1b1a141a0f170015000e131410001416191a17161616171b12111715151516,
    0x100c00001a1000151a161914101619130014001111130c00101518191a181a151818141619141019191b,
    0x80000160c0014141317100c16141000100010140d08000c1415141b1615191616101917130c14141b11,
    0x140800101314100c0810100f000f000c100c040008131313141719171b120c16180c081310161704,
    0x5140e0a12090d191b0d19161217190e12180e0900050d110e0012000d12110a0d11150e110009160000,
    0x101715150d111a1611151b181417191514170d00090c15110011001115150d1115181715000d1a000000,
    0x171716111517141517161413161a18131611000d0e1010001500151719111516151a1400111900000d0b,
    0x141414141610181b18131a141a17181316001117180c001400151419151b16121410001318000011150f,
    0x121010190c1518161414101b1614141b001516151200100017121a1416171b120c00141400001513150a,
    0xf0f140b16171612130f171813131d00191313160e0f00130f1713171717120b00131300001617131500,
    0x18101518141a19181b151617141d001d14181b1a190010191a1518141b151500141900001b1516170015,
    0xf19171314141717131614131b001d1314171b17170f141614171317191700131a000016191717001700,
    0x171d18131016141a1a111216001a1413161a1614121016101a1a181418001a17000018161a160014000a,
    0x1b141b0f10121416171b16001613171b1814131916100c141a161214001817000014141717001300150e,
    0x1016140e171314181a110017121416171018161b1a0810181b151000161900001213141900160016160f,
    0x1b111117161315151500111b1116140f141316150d0c1714160d00151a00001317111a00130012181107,
    0x1617151a171b1917001518151a131913141b1711181013191100161700001513101a001700191615110b,
    0x10101e1617171a0017151b161b171812161b151619141415001516000019150e1b001a0019151715150f,
    0xc1b1412141b001a19151414141718161b1914180d131400141500001a191a160014001a141519141413,
    0x141012121b001b171813131216141a171710171109100010190000191b181600100018121a1712131111,
    0xc1412170018141717161710101414160c16150d12000c1a000018141617000f0017141416191410120e,
    0x10161000141212161a170e0f1313180b191411150a08160000141217160012001613131217130e0f1500,
    0x1a0c00101212141f1411141a1a171514101416150e140000101617160015001216121417141114170006,
    0x8000c1614101b10151116141f18100f101417171400000c141414001900141710101412101114001012,
    0x81a120c140c10151b121b170f190e1316171005000810131000170010140f0c10160e1013000c1700]
  let code (a b : Fin 42) := ((rowCodes.getD a.val 0) >>> (8*b.val)) &&& 255
  let distance (a b : Fin 42) := code a b / 4
  let edgeStep (a b : Fin 42) : Fin 4 := Fin.ofNat 4 (code a b)
  have generators_ok : ∀ k : Fin 4, ∀ a b : Fin 42,
      (action k a=action k b ↔ a=b) ∧ edge (action k a) (action k b)=edge a b := by decide +kernel
  have descent_ok : ∀ a b : Fin 42, a≠b → edge a b=false →
      ((a=0 ∧ (b=1 ∨ b=22)) ∨ (b=0 ∧ (a=1 ∨ a=22))) ∨
      distance (action (edgeStep a b) a) (action (edgeStep a b) b)<distance a b := by decide +kernel
  have fast_orbit (a b : Fin 42) (ab : a≠b) (hn : edge a b=false) :
      ∃ f : Fin 42 → Fin 42, Function.Bijective f ∧ (∀ i j,edge (f i) (f j)=edge i j) ∧
        ∃ c : Fin 42, (c=1 ∨ c=22) ∧ ((f a=0 ∧ f b=c) ∨ (f a=c ∧ f b=0)) := by
    generalize hd:distance a b=n
    induction n using Nat.strong_induction_on generalizing a b with
    | ind n ih =>
      rcases descent_ok a b ab hn with clean|drop
      · refine ⟨id,Function.bijective_id,fun _ _=>rfl,?_⟩
        rcases clean with ⟨ha,hb⟩|⟨hb,ha⟩
        · exact ⟨b,hb,Or.inl ⟨ha,rfl⟩⟩
        · exact ⟨a,ha,Or.inr ⟨rfl,hb⟩⟩
      · let t:=action (edgeStep a b)
        have inject : Function.Injective t := fun {i j} e => ((generators_ok _ i j).1).mp e
        have bij : Function.Bijective t := ⟨inject,Finite.surjective_of_injective inject⟩
        have preserves (i j) : edge (t i) (t j)=edge i j := (generators_ok _ i j).2
        have less : distance (t a) (t b)<n := hd ▸ drop
        obtain ⟨f,hf,he,c,cs,hit⟩:=ih _ less (t a) (t b) (fun e=>ab (inject e)) ((preserves a b).trans hn) rfl
        exact ⟨f ∘ t,hf.comp bij,fun i j=>(he _ _).trans (preserves i j),c,cs,hit⟩

  have transport_present (f : Fin 42 → Fin 42) (hf : Function.Bijective f)
      (he : ∀ a b, edge (f a) (f b)=edge a b) (z : Fin 42 → Bool) :
      present (fun i => z (f i)) ↔ present z := by
    rw [symm_present,symm_present]
    constructor
    · rintro ⟨a,b,h,ha,hb⟩
      exact ⟨f a,f b,(he a b).trans h,ha,hb⟩
    · rintro ⟨a,b,h,ha,hb⟩
      obtain ⟨a,rfl⟩ := hf.2 a
      obtain ⟨b,rfl⟩ := hf.2 b
      exact ⟨a,b,(he a b).symm.trans h,ha,hb⟩
  let run (gs : List Gate) (w : List Bool) := gs.foldl (fun v g=>v++[evaluate g v]) w
  let lew (w v : List Bool) := ∀ i, w.getD i false=true → v.getD i false=true
  let good (gs : List Gate) := ∀ g∈gs, g.op=.and ∨ g.op=.or

  have step_mono (w v : List Bool) (g : Gate) (ho : g.op=.and ∨ g.op=.or)
      (hs : lew w v) : evaluate g w=true → evaluate g v=true := by
    rcases ho with ha | ha
    · unfold evaluate;rw [ha]
      change (g.inputs.map _).all id=true → (g.inputs.map _).all id=true
      intro hall
      apply List.all_eq_true.mpr
      rintro k hk
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hk
      exact hs i (List.all_eq_true.mp hall _ (List.mem_map_of_mem hi))
    · unfold evaluate;rw [ha]
      change (g.inputs.map _).any id=true → (g.inputs.map _).any id=true
      intro h
      obtain ⟨k,hk,ht⟩ := List.any_eq_true.mp h
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hk
      exact List.any_eq_true.mpr ⟨_,List.mem_map_of_mem hi,hs i ht⟩

  have snoc_mono {w v : List Bool} {b c : Bool} (hl : w.length=v.length)
      (h : lew w v) (hb : b=true→c=true) : lew (w++[b]) (v++[c]) := by
    intro i hi
    by_cases lt : i<w.length
    · rw [List.getD_append _ _ _ _ lt] at hi
      rw [List.getD_append _ _ _ _ (by omega)]
      exact h i hi
    by_cases eq : i=w.length
    · subst i
      simpa [←hl] using (hb (by simpa using hi))
    · rw [List.getD_eq_default _ _ (by simp;omega)] at hi
      contradiction

  have run_mono (gs : List Gate) (hg : good gs) (w v : List Bool) (hl : w.length=v.length)
      (hs : lew w v) : lew (run gs w) (run gs v) := by
    induction gs generalizing w v with
    | nil => exact hs
    | cons g gs ih =>
      apply ih (fun o h=>hg o (List.mem_cons_of_mem _ h)) _ _ (by simp [hl])
      exact snoc_mono hl hs (step_mono w v g (hg g (by simp)) hs)

  have input_mono (z t : Fin 42 → Bool) (hz : ∀ a, z a=true → t a=true) :
      lew (List.ofFn z) (List.ofFn t) := by
    intro i hi
    by_cases h:i<42
    · rw [List.getD_eq_getElem _ _ (by simpa using h),List.getElem_ofFn] at hi ⊢
      exact hz ⟨i,h⟩ hi
    · rw [List.getD_eq_default _ _ (by simp;omega)] at hi
      contradiction

  have overall_mono (gs : List Gate) (hg : good gs) (out : Nat) (z t : Fin 42 → Bool)
      (hz : ∀ a, z a=true → t a=true) :
      (Circuit.mk gs out).eval (List.ofFn z)=true →
      (Circuit.mk gs out).eval (List.ofFn t)=true :=
    run_mono gs hg _ _ (by simp) (input_mono z t hz) out

  have splice_eval (pre post : List Gate) (g : Gate) (out : Nat) (z : Fin 42 → Bool) :
      (Circuit.mk (pre++g::post) out).eval (List.ofFn z) =
        (run post (values pre z++[evaluate g (values pre z)])).getD out false := by
    change (run (pre++g::post) (List.ofFn z)).getD out false=_
    unfold run
    rw [List.foldl_append];rfl

  have source_read (gs : List Gate) (z : Fin 42 → Bool) (a : Fin 42) :
      (values gs z).getD a.val false=z a := by
    have eq := old_wires [] gs z (i:=a.val) (by simp)
    simp only [List.nil_append,prefix_nil] at eq
    exact eq.trans (by rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn])

  let correct (C : Circuit) := ∀ z : Fin 42 → Bool, C.eval (List.ofFn z)=true ↔ present z
  let nullGate : Gate := ⟨.or,[]⟩
  let identityGate (a : Fin 42) : Gate := ⟨.or,[a.val]⟩

  have replace_zero_on_edges (pre post : List Gate) (g : Gate) (out : Nat)
      (hgPre : good pre) (hgPost : good post) (hc : correct ⟨pre++g::post,out⟩)
      (hz : ∀ a b, edge a b=true → evaluate g (values pre (pairInput (a,b)))=false) :
      correct ⟨pre++nullGate::post,out⟩ := by
    intro z
    constructor
    · intro hyp
      apply (hc z).mp
      rw [splice_eval] at hyp ⊢
      have e : evaluate nullGate (values pre z)=false := rfl
      rw [e] at hyp
      apply run_mono post hgPost _ _ (by simp)
        (snoc_mono rfl (fun _ h=>h) (fun h=>Bool.noConfusion h)) out hyp
    · intro h
      obtain ⟨a,b,he,ha,hb⟩ := (symm_present z).mp h
      let p := pairInput (a,b)
      have hp : present p := (symm_present p).mpr
        ⟨a,b,he,by simp [p,pairInput],by simp [p,pairInput]⟩
      have old := (hc p).mpr hp
      have new : (Circuit.mk (pre++nullGate::post) out).eval (List.ofFn p)=true := by
        rw [splice_eval] at old ⊢
        change (run post (values pre p++[false])).getD out false=true
        rw [hz a b he] at old
        exact old
      apply overall_mono _ _ out p z _ new
      · intro q hq
        rcases List.mem_append.mp hq with hq | hq
        · exact hgPre _ hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact Or.inr rfl
        · exact hgPost _ hq
      · intro i hi
        rcases (of_decide_eq_true hi : i=a ∨ i=b) with rfl | rfl
        · exact ha
        · exact hb

  have direct_singleton (pre post : List Gate) (g : Gate) (out : Nat) (a : Fin 42) (hg : g.op=.and)
      (hin : a.val∈g.inputs) (hpre : good pre)
      (hon : evaluate g (values pre (fun i => decide (i=a)))=true) :
      ∀ z : Fin 42 → Bool, (Circuit.mk (pre++g::post) out).eval (List.ofFn z) =
        (Circuit.mk (pre++identityGate a::post) out).eval (List.ofFn z) := by
    intro z
    have e : evaluate g (values pre z)=z a := by
      cases hv : z a with
      | true =>
        apply step_mono _ _ _ (Or.inl hg) _ hon
        apply run_mono pre hpre _ _ (by simp) (input_mono _ z ?_)
        intro i h; obtain rfl : i=a := of_decide_eq_true h; exact hv
      | false =>
        apply Bool.eq_false_iff.mpr
        intro ht
        unfold evaluate at ht;rw [hg] at ht
        change (g.inputs.map _).all id=true at ht
        have v := List.all_eq_true.mp ht _ (List.mem_map_of_mem hin)
        change (values pre z).getD a.val false=true at v
        rw [source_read,hv] at v
        contradiction
    rw [splice_eval,splice_eval,e]
    have ide : evaluate (identityGate a) (values pre z)=z a := by
      change ((values pre z).getD a.val false || false)=_
      rw [source_read];simp
    rw [ide]
  let number (C : Circuit) : Nat := by classical exact C.gates.countP (fun g=>decide (g.op=.and))
  let beta (C : Circuit) := Monotone2 C ∧ C.size≤124 ∧ correct C

  let irreducible (C : Circuit) : Prop :=
    ∀ pre post (g : Gate), C.gates=pre++g::post → g.op=.and →
      (∃ a b, edge a b=true ∧ evaluate g (values pre (pairInput (a,b)))=true) ∧
        ∀ a : Fin 42, a.val∈g.inputs → evaluate g (values pre (fun i=>decide (i=a)))=false

  have exists_min (C : Circuit) (hC : beta C) : ∃ D, beta D ∧ ∀ C', beta C' → number D ≤ number C' := by
    classical
    let P (n : Nat) := ∃ D, beta D ∧ number D=n
    have existsP : ∃ n, P n := ⟨_,C,hC,rfl⟩
    obtain ⟨D,hD,hn⟩ := Nat.find_spec existsP
    refine ⟨D,hD,fun Q hQ => ?_⟩
    rw [hn]
    exact Nat.find_min' existsP (show P (number Q) from ⟨Q,hQ,rfl⟩)

  have irreducible_of_min (D : Circuit) (hD : beta D) (hmin : ∀ Q, beta Q → number D ≤ number Q) : irreducible D := by
    classical
    obtain ⟨hm,hs,hc⟩ := hD
    intro pre post g hg hopen
    have hp : good pre := fun k hk => (hm k (hg ▸ List.mem_append_left _ hk)).1
    have ht : good post := fun k hk => (hm k (hg ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hk))).1
    have exclude (v : Gate) (hv : v.op=.or) (hl : v.inputs.length ≤ 2)
        (hvC : correct ⟨pre++v::post,D.output⟩) : False := by
      let D' : Circuit := ⟨pre++v::post,D.output⟩
      have hnew : beta D' := by
        refine ⟨?_,?_,hvC⟩
        · intro o ho
          change o ∈ pre++v::post at ho
          rcases List.mem_append.mp ho with ho | ho
          · apply hm; rw [hg]; simp [ho]
          rcases List.mem_cons.mp ho with rfl | ho
          · exact ⟨Or.inr hv,hl⟩
          · apply hm; rw [hg];simp [ho]
        · change (pre++v::post).length ≤ 124
          change D.gates.length≤124 at hs
          rw [hg] at hs; simpa using hs
      have low : number D'<number D := by
        change (pre++v::post).countP (fun o=>decide (o.op=.and)) < D.gates.countP (fun o=>decide (o.op=.and))
        rw [hg]
        simp [List.countP_append,hopen,hv]
      have bound := hmin D' hnew
      omega
    constructor
    · by_contra! bad
      apply exclude nullGate rfl (by decide)
      apply replace_zero_on_edges _ _ _ _ hp ht _ (by
        intro a b ha; simpa using bad a b ha)
      have eqD : (Circuit.mk (pre++g::post) D.output)=D := congrArg (fun l => Circuit.mk l D.output) hg.symm
      rwa [eqD]
    · intro a ha
      cases h : evaluate g (values pre (fun i=>decide (i=a))) with
      | false => rfl
      | true =>
        exfalso
        apply exclude (identityGate a) rfl (by change 1≤2;decide)
        intro z
        have eq := direct_singleton pre post g D.output a hopen ha hp h z
        rw [←eq]
        have eqD : (Circuit.mk (pre++g::post) D.output)=D := congrArg (fun l => Circuit.mk l D.output) hg.symm
        rw [eqD]
        exact hc z
  let allpairs : List (Fin 42 × Fin 42) := (List.finRange 42).flatMap fun a =>
    ((List.finRange 42).filter fun b=>a≠b ∧ edge a b=false).map fun b=>(a,b)
  have member (a b : Fin 42) : (a,b)∈allpairs ↔ a≠b ∧ edge a b=false := by
    simp [allpairs]
  have allpairs_cover (z : Fin 42 → Bool) (hi : ¬ present z) (a b : Fin 42) (ha : z a=true) (hb : z b=true) :
      ∃ p∈allpairs, (a=p.1 ∨ a=p.2) ∧ (b=p.1 ∨ b=p.2) := by
    by_cases h:a=b
    · subst b
      have witness : ∀ a : Fin 42, ∃ b : Fin 42, a≠b ∧ edge a b=false := by decide +kernel
      obtain ⟨b,hab,hn⟩ := witness a
      exact ⟨(a,b),(member a b).mpr ⟨hab,hn⟩,Or.inl rfl,Or.inl rfl⟩
    · have n : edge a b=false := Bool.eq_false_iff.mpr (fun he=>hi ((symm_present z).mpr ⟨a,b,he,ha,hb⟩))
      exact ⟨(a,b),(member a b).mpr ⟨h,n⟩,Or.inl rfl,Or.inr rfl⟩

  have number_rename (f : Fin 42 → Fin 42) (C : Circuit) : number (renamed f C)=number C := by
    classical
    change (C.gates.map (move f)).countP (fun o=>decide (o.op=.and))=C.gates.countP (fun o=>decide (o.op=.and))
    rw [List.countP_map];rfl
  intro C hm hs _
  by_contra! ok
  obtain ⟨D,hD,hmin⟩ := exists_min C ⟨hm,hs,ok⟩
  obtain ⟨z,hi,on⟩ := dirty D hD
  have inhab : ∃ p,p∈allpairs := ⟨(0,1),(member _ _).mpr (by decide)⟩
  obtain ⟨⟨a,b⟩,hab,hit⟩ := dirty_pair D hD.1 z allpairs inhab (allpairs_cover z hi) on
  obtain ⟨f,hf,he,j,hj,img⟩ := fast_orbit a b ((member a b).mp hab).1 ((member a b).mp hab).2
  let E := renamed f D
  have hE : beta E := by
    refine ⟨renamed_mono f D hD.1,?_,?_⟩
    · change (D.gates.map (move f)).length ≤ 124
      rw [List.length_map];exact hD.2.1
    · intro x
      rw [renamed_eval]
      exact (hD.2.2 _).trans (transport_present f hf he x)
  have minimumE (Q : Circuit) (hQ : beta Q) : number E ≤ number Q := (number_rename f D) ▸ hmin Q hQ
  have strong := irreducible_of_min E hE minimumE
  have commuted : pairInput (f a,f b)=pairInput (0,j) := by
    rcases img with ⟨ha,hb⟩|⟨ha,hb⟩
    · rw [ha,hb]
    · rw [ha,hb]; funext i;exact Bool.eq_iff_iff.mpr (by simp [pairInput,or_comm])
  have pull : (fun i=>pairInput (f a,f b) (f i))=pairInput (a,b) := by
    funext i;simp only [pairInput,hf.1.eq_iff]
  have awakeE := renamed_awake f D (pairInput (f a,f b)) (pull.symm ▸ hit)
  rw [commuted] at awakeE
  have bad : ∃ x, ¬ (E.eval (List.ofFn x)=true ↔ present x) := by
    rcases hj with rfl|rfl
    · exact side E hE.1 hE.2.1 strong awakeE
    · exact crossing E hE.1 hE.2.1 strong awakeE
  obtain ⟨x,hx⟩ := bad
  exact hx (hE.2.2 x)

