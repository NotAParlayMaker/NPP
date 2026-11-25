import PEqualNP.Defs

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_4055_314
    (twoPoints :
      let I := Fin 21 × Fin 5
      let pt (e : I) : Fin 42 := Fin.castAdd 21 e.1
      let ln (e : I) : Fin 42 := Fin.natAdd 21 (e.1 + ![20,0,5,7,17] e.2)
      let star (v : Fin 42) := Finset.univ.filter (fun e : I => pt e = v ∨ ln e = v)
      let grow (F : Set (Finset I)) (r : Finset I × Finset I) : Set (Finset I) :=
        {s | s ∈ F ∨ r.1 ∈ F ∧ r.2 ∈ F ∧ s ⊆ r.1 ∪ r.2}
      let seed (Z : Finset (Fin 42)) : Set (Finset I) :=
        {s | s = ∅ ∨ ∃ v ∈ Z, s ⊆ star v}
    ∀ (q : List (Finset I × Finset I)) (T : Finset I),
        (∀ Z, (∀ e : I, ∃ v ∈ Z, e ∈ star v) →
          T ∈ q.foldl grow (grow (seed Z) (star 0,star 1))) → T.card ≤ q.length+2
    )
    (incident :
      let I := Fin 21 × Fin 5
      let pt (e : I) : Fin 42 := Fin.castAdd 21 e.1
      let ln (e : I) : Fin 42 := Fin.natAdd 21 (e.1 + ![20,0,5,7,17] e.2)
      let star (v : Fin 42) := Finset.univ.filter (fun e : I => pt e = v ∨ ln e = v)
      let grow (F : Set (Finset I)) (r : Finset I × Finset I) : Set (Finset I) :=
        {s | s ∈ F ∨ r.1 ∈ F ∧ r.2 ∈ F ∧ s ⊆ r.1 ∪ r.2}
      let seed (Z : Finset (Fin 42)) : Set (Finset I) :=
        {s | s = ∅ ∨ ∃ v ∈ Z, s ⊆ star v}
    ∀ (q : List (Finset I × Finset I)) (T : Finset I),
        (∀ Z, (∀ e : I, ∃ v ∈ Z, e ∈ star v) →
          T ∈ q.foldl grow (grow (seed Z) (star 0,star 21))) → T.card ≤ q.length+2
    )
    (nonincident :
      let I := Fin 21 × Fin 5
      let pt (e : I) : Fin 42 := Fin.castAdd 21 e.1
      let ln (e : I) : Fin 42 := Fin.natAdd 21 (e.1 + ![20,0,5,7,17] e.2)
      let star (v : Fin 42) := Finset.univ.filter (fun e : I => pt e = v ∨ ln e = v)
      let grow (F : Set (Finset I)) (r : Finset I × Finset I) : Set (Finset I) :=
        {s | s ∈ F ∨ r.1 ∈ F ∧ r.2 ∈ F ∧ s ⊆ r.1 ∪ r.2}
      let seed (Z : Finset (Fin 42)) : Set (Finset I) :=
        {s | s = ∅ ∨ ∃ v ∈ Z, s ⊆ star v}
    ∀ (q : List (Finset I × Finset I)) (T : Finset I),
        (∀ Z, (∀ e : I, ∃ v ∈ Z, e ∈ star v) →
          T ∈ q.foldl grow (grow (seed Z) (star 0,star 22))) → T.card ≤ q.length+2
    )
:
∀ (x1 : List (Finset ℕ × Finset ℕ)) (x2 : Finset ℕ),   have x3 : Fin (21 : ℕ) → Fin (21 : ℕ) → Bool := fun (x3 x4 : Fin (21 : ℕ)) => [(↑x3 + (20 : ℕ)) % (21 : ℕ), ↑x3, (↑x3 + (5 : ℕ)) % (21 : ℕ), (↑x3 + (7 : ℕ)) % (21 : ℕ), (↑x3 + (17 : ℕ)) % (21 : ℕ)].contains ↑x4;   have x4 : (Fin (42 : ℕ) → Bool) → Bool := fun (x4 : Fin (42 : ℕ) → Bool) =>     have x5 : List Bool := List.foldl (fun (x5 : List Bool) (x6 : Finset ℕ × Finset ℕ) => x5 ++ [Decidable.decide (∀ x7 ∈ x6.1, x5.getD x7 Bool.false = Bool.true) || Decidable.decide (∀ x7 ∈ x6.2, x5.getD x7 Bool.false = Bool.true)]) (List.ofFn x4 ++ [Bool.false]) x1;     Decidable.decide (∀ x6 ∈ x2, x5.getD x6 Bool.false = Bool.true);   have x5 : (Fin (42 : ℕ) → Bool) → Prop := fun (x5 : Fin (42 : ℕ) → Bool) => ∀ (x6 x7 : Fin (21 : ℕ)), x3 x6 x7 = Bool.true → x5 (Fin.castAdd (21 : ℕ) x6) = Bool.false ∨ x5 (Fin.natAdd (21 : ℕ) x7) = Bool.false;   (∀ (x6 : ℕ) (x7 : x6 < x1.length), ∀ x8 ∈ x1[x6].1 ∪ x1[x6].2, x8 < (43 : ℕ) + x6) → (∀ x7 ∈ x2, x7 < (43 : ℕ) + x1.length) → (∀ (x8 x9 : Fin (21 : ℕ)), x3 x8 x9 = Bool.true → (x4 fun (x11 : Fin (42 : ℕ)) => Decidable.decide (x11 = Fin.castAdd (21 : ℕ) x8 ∨ x11 = Fin.natAdd (21 : ℕ) x9)) = Bool.true) → (∀ (x9 : Fin (42 : ℕ) → Bool), x5 x9 → (∀ (x11 : Fin (42 : ℕ) → Bool), x5 x11 → (∀ (x13 : Fin (42 : ℕ)), x9 x13 = Bool.true → x11 x13 = Bool.true) → x11 = x9) → x4 x9 = Bool.false) → (104 : ℕ) ≤ x1.length := by
  intro R out posted eval indep _ _ pos neg
  classical
  let I := Fin 21 × Fin 5
  let pt (e : I) : Fin 42 := Fin.castAdd 21 e.1
  let ln (e : I) : Fin 42 := Fin.natAdd 21 (e.1 + ![20,0,5,7,17] e.2)
  let star (v : Fin 42) := Finset.univ.filter (fun e : I => pt e = v ∨ ln e = v)
  have allCover : ∀ e : I, ∃ v ∈ (Finset.univ : Finset (Fin 42)), e ∈ star v := by
    intro e
    exact ⟨pt e,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl rfl⟩⟩
  have avoid (v : Fin 42) : ∀ e : I, ∃ w ∈ Finset.univ.erase v, e ∈ star w := by
    intro e
    by_cases hp : pt e = v
    · have ne : ln e ≠ v := by
        rw [← hp]
        intro eq
        have := congrArg Fin.val eq
        simp [pt,ln] at this
        omega
      exact ⟨ln e,Finset.mem_erase.mpr ⟨ne,Finset.mem_univ _⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inr rfl⟩⟩
    · exact ⟨pt e,Finset.mem_erase.mpr ⟨hp,Finset.mem_univ _⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl rfl⟩⟩
  have distinctEnds (e f : I) : pt e ≠ ln f := by
    intro eq
    have h := congrArg Fin.val eq
    simp [pt,ln] at h
    omega
  have identify : ∀ (p q : Fin 21) (i j : Fin 5),
      pt (p,i) = pt (q,j) → ln (p,i) = ln (q,j) → (p,i) = (q,j) := by decide +kernel
  have unique {a : Finset I} {v w : Fin 42} (ha : 1 < a.card)
      (hv : a ⊆ star v) (hw : a ⊆ star w) : v=w := by
    by_contra ne
    obtain ⟨e,he,f,hf,diff⟩ := Finset.one_lt_card.mp ha
    have orient (i : I) (hi : i ∈ a) :
        (pt i = v ∧ ln i = w) ∨ (pt i = w ∧ ln i = v) := by
      rcases (Finset.mem_filter.mp (hv hi)).2 with h | h <;>
        rcases (Finset.mem_filter.mp (hw hi)).2 with k | k
      · exact (ne (h.symm.trans k)).elim
      · exact Or.inl ⟨h,k⟩
      · exact Or.inr ⟨k,h⟩
      · exact (ne (h.symm.trans k)).elim
    rcases orient e he with ⟨p,l⟩ | ⟨p,l⟩ <;> rcases orient f hf with ⟨p',l'⟩ | ⟨p',l'⟩
    · exact diff (identify e.1 f.1 e.2 f.2 (p.trans p'.symm) (l.trans l'.symm))
    · exact distinctEnds e f (p.trans l'.symm)
    · exact distinctEnds e f (p.trans l'.symm)
    · exact diff (identify e.1 f.1 e.2 f.2 (p.trans p'.symm) (l.trans l'.symm))
  let grow (F : Set (Finset I)) (r : Finset I × Finset I) : Set (Finset I) :=
    {s | s ∈ F ∨ r.1 ∈ F ∧ r.2 ∈ F ∧ s ⊆ r.1 ∪ r.2}
  let seed (Z : Finset (Fin 42)) : Set (Finset I) :=
    {s | s = ∅ ∨ ∃ v ∈ Z, s ⊆ star v}
  let covers (Z : Finset (Fin 42)) := ∀ e : I, ∃ v ∈ Z, e ∈ star v
  let wins (rs : List (Finset I × Finset I)) (s : Finset I) :=
    ∀ Z, covers Z → s ∈ rs.foldl grow (seed Z)
  let cap (v w : Fin 42) := ∀ (q : List (Finset I × Finset I)) (T : Finset I),
    (∀ Z, covers Z → T ∈ q.foldl grow (grow (seed Z) (star v,star w))) → T.card ≤ q.length+2
  have transfer (f : I ≃ I) (g : Fin 42 ≃ Fin 42)
      (inc : ∀ e v, e ∈ star v ↔ f e ∈ star (g v)) (v w : Fin 42) :
      cap (g v) (g w) → cap v w := by
    intro bound q T hT
    let mapS (a : Finset I) := a.map f.toEmbedding
    let mapR (r : Finset I × Finset I) := (mapS r.1,mapS r.2)
    have starMap (z) : mapS (star z) = star (g z) := by
      ext e
      obtain ⟨u,rfl⟩ := f.surjective e
      simpa [mapS] using inc u z
    have sim (rs : List (Finset I × Finset I)) (F G : Set (Finset I))
        (init : ∀ a ∈ F, mapS a ∈ G) :
        ∀ a ∈ rs.foldl grow F, mapS a ∈ (rs.map mapR).foldl grow G := by
      induction rs generalizing F G with
      | nil => exact init
      | cons r tail ih =>
        simp only [List.foldl_cons,List.map_cons]
        apply ih
        rintro s (old | ⟨ha,hb,sub⟩)
        · exact Or.inl (init _ old)
        · refine Or.inr ⟨init _ ha,init _ hb,?_⟩
          change mapS s ⊆ mapS r.1 ∪ mapS r.2
          rw [← Finset.map_union]
          exact Finset.map_subset_map.mpr sub
    have out := bound (q.map mapR) (mapS T) (by
      intro Y hY
      let Z := Finset.univ.filter (fun z => g z ∈ Y)
      have hz : covers Z := by
        intro e
        obtain ⟨u,hu,he⟩ := hY (f e)
        obtain ⟨z,rfl⟩ := g.surjective u
        exact ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩,(inc e z).mpr he⟩
      have init : ∀ a ∈ seed Z, mapS a ∈ seed Y := by
        rintro s (rfl | ⟨u,hu,sub⟩)
        · exact Or.inl (Finset.map_empty _)
        · exact Or.inr ⟨g u,(Finset.mem_filter.mp hu).2,
            starMap u ▸ (Finset.map_subset_map.mpr sub : mapS s ⊆ mapS (star u))⟩
      apply sim q _ _ _ T (hT Z hz)
      rintro s (old | ⟨h1,h2,sub⟩)
      · exact Or.inl (init _ old)
      · refine Or.inr ⟨starMap v ▸ init _ h1,starMap w ▸ init _ h2,?_⟩
        rw [← starMap v,← starMap w,← Finset.map_union]
        exact Finset.map_subset_map.mpr sub)
    simpa [mapS] using out
  let K := Fin 3
  let vertexCodes : K → ℕ := ![
    2448204547216469137018651953218882031453209215241654587828570447030074224769,
    116696487011656533558650526589758534724749606585849649371536356090713115221,
    4345710715711030795663915292453503455475135276148599564295587875467853042240]
  let inverseVertexCodes : K → ℕ := ![
    4593100793474418875535010569993777399783255722076117737154020136294642356244,
    116696487011656533558650526589758534724749606585849649371536356090713115221,
    3004292923316813423590327126191357660177048424005369226179936949885237239936]
  let edgeCodes : K → ℕ := ![
    5681294872732850988167415489547669725229787803761781188639968334617289680078226313007462939508894922374191576464761424184021406777055995940528701043464184836512449792955798892357776316270635518567048312677904293707236101,
    41816146087918051383707221826452464402433295827837438311146140601450204915541709798881493849893412126489102320826030369894956809153239126296787420283046202942778351635522943505635470281420080794636379749524282331293319301,
    73980359411072473256033263308566852055425424094681621357918296696263688988674758648897884483349425999055087114147840555422170239900421756069558886750639061606620615469566530387364324441364181992825294945346543969670004996]
  let inverseEdgeCodes : K → ℕ := ![
    140878183600241891238466648106428248240771663978366550249889184747198856560187438936838328713753488585948303661903607782176863391695745575273600696101513096459983258824212614070413810315841602085359102330928519701574824676,
    41816146087918051383707221826452464402433295827837438311146140601450204915541709798881493849893412126489102320826030369894956809153239126296787420283046202942778351635522943505635470281420080794636379749524282331293319301,
    135208094440870598277531173206220408726642820607895809879056854040060319801559380277150999920910493519014673552837375245730650055547272726394951757593788516564702758099351566823715384511503067344323340829545588942417445250]
  let distanceCodes : Fin 42 → ℕ := ![
    159391557444728365561039496147695569976145941662916731071595520,
    320041524880529985062830983994229248175593366628033098172992518,
    369856605689318558380508826001122136023199053868535257819644103,
    263899122363241561677680273232623045138665046421425193680377062,
    318487891582228441267851345756753435195237081920490332607453444,
    371614091593715999137451044026316776468979294595709594504503463,
    321649983161908951463588218262452769362488113817024323888847047,
    421330407761156605041069345242656070963328078460946522396925157,
    368350049262216458339947783851426988921055460346493987360839943,
    369856556698756377796108561695926414525824205746296903218404551,
    265455845078177160073667190719619479983550875636901723815222536,
    213983466790476227580196509253954855836536626375287022499864804,
    315321141264087539129615577996488790045198222476996358724393190,
    215643858280651982579101039483408329250012879349812501881724166,
    316929648531400156010675663564880365712441525255118496351853767,
    217299342622965671314831169561998270180926098260355725057563846,
    318530208428041875797658971276720996598087660454173576408536291,
    266959163482926578714329360634718588294441945382941830467002565,
    262089701715874084635287413038025027895975511309066211483196549,
    106266974307329086638393474568272552597647739045271117773343874,
    58061778341703064455243095449866359044655251068886776717449281,
    54946817224166171797381381386580965958378763578195329185648769,
    162563216441727385431235130737886829444605953193159207044682818,
    263850528507035037054308631486422990474171953156523368697203813,
    267114523233940522815397812528952289094362462834263432137674949,
    268718321102048464493378320134462443373426387001518128045922502,
    318533346977408657000720433092804352600995987071310411661056228,
    370004068490813532093894782554150886364278840080969491937466532,
    373070523108823788644172607140029854857196361631611898615272674,
    422940435315025817824446599128673317339851898174150459513838726,
    320244008875502610537978107328633699932003224057430245878533283,
    426201484727628133966667129035682903927281682805512248958849189,
    424594453154737334947131735839394742027132651129088176308852935,
    373122315469971810931689537784632819748523219832957166175853766,
    371565595811378083378987075767100474178084966587497394952444104,
    421330457996873061009840829346952334471438183821568447118284006,
    265507623505016487250415809460894337068877049585511464578457830,
    217350932698116275911450025490100515243268650814715721886702854,
    371554411622954841584979984356379973394876569979319513330687139,
    421024300970393497953796321982514435154397304266928226239222983,
    257267319888046366283681574787839870869019409410216819593188581,
    3375862793572543760202009498119537430374292223106802980624548]
  let vertex (k : K) (v : Fin 42) : Fin 42 := ⟨((vertexCodes k / 2^(6*v.val)) % 64)%42,by omega⟩
  let vertexInv (k : K) (v : Fin 42) : Fin 42 := ⟨((inverseVertexCodes k / 2^(6*v.val)) % 64)%42,by omega⟩
  let index (e : I) := 5*e.1.val+e.2.val
  let decode (j : ℕ) : I := (⟨(j/5)%21,by omega⟩,⟨j%5,by omega⟩)
  let edge (k : K) (e : I) := decode ((edgeCodes k / 2^(7*index e)) % 128)
  let edgeInv (k : K) (e : I) := decode ((inverseEdgeCodes k / 2^(7*index e)) % 128)
  let rank (v w : Fin 42) := (distanceCodes v / 2^(5*w.val)) % 32
  have vit : (∀ k v, vertexInv k (vertex k v) = v) ∧
      (∀ k v, vertex k (vertexInv k v) = v) := by decide +kernel
  have eit : (∀ k p l, edgeInv k (edge k (p,l)) = (p,l)) ∧
      (∀ k p l, edge k (edgeInv k (p,l)) = (p,l)) := by decide +kernel
  have incidence : ∀ k p i v,
      (pt (p,i) = v ∨ ln (p,i) = v) ↔
      (pt (edge k (p,i)) = vertex k v ∨ ln (edge k (p,i)) = vertex k v) := by decide +kernel
  have desc : ∀ v w : Fin 42, v ≠ w →
      (v=0 ∧ w=1) ∨ (v=0 ∧ w=21) ∨ (v=0 ∧ w=22) ∨
      ∃ k, rank (vertex k v) (vertex k w) < rank v w := by decide +kernel
  have obstruction (v w : Fin 42) (ne : v ≠ w) : cap v w := by
    have along (n : ℕ) : ∀ v w, rank v w = n → v ≠ w → cap v w := by
      induction n using Nat.strong_induction_on with
      | ind n ih =>
        intro v w hn ne
        rcases desc v w ne with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨k,lower⟩
        · exact twoPoints
        · exact incident
        · exact nonincident
        · let f : I ≃ I := ⟨edge k,edgeInv k,fun e => eit.1 k e.1 e.2,fun e => eit.2 k e.1 e.2⟩
          let g : Fin 42 ≃ Fin 42 := ⟨vertex k,vertexInv k,vit.1 k,vit.2 k⟩
          have ok (e : I) (z : Fin 42) : e ∈ star z ↔ f e ∈ star (g z) := by
            obtain ⟨p,i⟩ := e
            simp only [star,Finset.mem_filter,Finset.mem_univ,true_and]
            change (pt (p,i) = z ∨ ln (p,i) = z) ↔
              (pt (edge k (p,i)) = vertex k z ∨ ln (edge k (p,i)) = vertex k z)
            exact incidence k p i z
          exact transfer f g ok v w (ih _ (hn ▸ lower) _ _ rfl (fun eq => ne (g.injective eq)))
    exact along _ v w rfl ne
  have down {Z : Finset (Fin 42)} {a b : Finset I} (ha : a ∈ seed Z) (sub : b ⊆ a) :
      b ∈ seed Z := by
    rcases ha with rfl | ⟨v,hv,h⟩
    · exact Or.inl (Finset.subset_empty.mp sub)
    · exact Or.inr ⟨v,hv,sub.trans h⟩
  have mon (Q : List (Finset I × Finset I)) (F G : Set (Finset I)) (inc : F ⊆ G) :
      Q.foldl grow F ⊆ Q.foldl grow G := by
    induction Q generalizing F G with
    | nil => exact inc
    | cons r q ih =>
      apply ih
      rintro s (old | ⟨ha,hb,sub⟩)
      · exact Or.inl (inc old)
      · exact Or.inr ⟨inc ha,inc hb,sub⟩
  have eraseRun (Q : List (Finset I × Finset I)) (c : Finset I) (F G : Set (Finset I))
      (init : ∀ a ∈ F, a \ c ∈ G) : ∀ a ∈ Q.foldl grow F,
      a \ c ∈ (Q.map (fun r => (r.1 \ c,r.2 \ c))).foldl grow G := by
    induction Q generalizing F G with
    | nil => exact init
    | cons r q ih =>
      simp only [List.map_cons,List.foldl_cons]
      apply ih
      rintro s (old | ⟨ha,hb,sub⟩)
      · exact Or.inl (init _ old)
      · refine Or.inr ⟨init _ ha,init _ hb,?_⟩
        intro e he
        obtain ⟨hs,hc⟩ := Finset.mem_sdiff.mp he
        rcases Finset.mem_union.mp (sub hs) with h | h
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h,hc⟩)
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h,hc⟩)
  have centered {a : Finset I} {Z : Finset (Fin 42)} (big : 1 < a.card) (ha : a ∈ seed Z) :
      ∃ v ∈ Z, a ⊆ star v := by
    rcases ha with rfl | h
    · simp at big
    · exact h
  have game (k : ℕ) : ∀ (Q : List (Finset I × Finset I)) (T : Finset I),
      Q.length = k → wins Q T → T.card ≤ k+1 := by
    induction k with
    | zero =>
      intro Q T hq solved
      have nil : Q=[] := List.length_eq_zero_iff.mp hq
      subst Q
      by_contra! big
      obtain ⟨v,_,hv⟩ := centered big (solved Finset.univ allCover)
      obtain ⟨w,hw,hsub⟩ := centered big (solved (Finset.univ.erase v) (avoid v))
      exact (Finset.mem_erase.mp hw).1 (unique big hsub hv)
    | succ k ih =>
      intro Q T hq solved
      cases Q with
      | nil => simp at hq
      | cons r q =>
        have len : q.length=k := by simpa using hq
        have cheap (c : Finset I) (low : c.card ≤ 1)
            (which : r.1 = c ∨ r.2 = c) : T.card ≤ k+1+1 := by
          have win : wins (q.map (fun p => (p.1 \ c,p.2 \ c))) (T \ c) := by
            intro Z hz
            apply eraseRun q c (grow (seed Z) r) (seed Z) _ T (solved Z hz)
            rintro s (old | ⟨ha,hb,sub⟩)
            · exact down old Finset.sdiff_subset
            · rcases which with h | h
              · apply down hb
                intro e he
                have hh := Finset.mem_sdiff.mp he
                exact (Finset.mem_union.mp (sub hh.1)).resolve_left (h ▸ hh.2)
              · apply down ha
                intro e he
                have hh := Finset.mem_sdiff.mp he
                exact (Finset.mem_union.mp (sub hh.1)).resolve_right (h ▸ hh.2)
          have bound := ih _ _ (by simpa using len) win
          have sub : T ⊆ (T \ c) ∪ c := by
            intro e he
            by_cases hc : e∈c
            · exact Finset.mem_union_right _ hc
            · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he,hc⟩)
          have size := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
          omega
        by_cases aSmall : r.1.card ≤ 1
        · exact cheap _ aSmall (Or.inl rfl)
        by_cases bSmall : r.2.card ≤ 1
        · exact cheap _ bSmall (Or.inr rfl)
        have aBig : 1 < r.1.card := by omega
        have bBig : 1 < r.2.card := by omega
        have discard (h : ∀ Z, covers Z → grow (seed Z) r ⊆ seed Z) : T.card ≤ k+1+1 := by
          have win : wins q T := fun Z hz => mon q _ _ (h Z hz) (solved Z hz)
          have := ih q T len win
          omega
        by_cases active : ∃ Z, covers Z ∧ r.1 ∈ seed Z ∧ r.2 ∈ seed Z
        · obtain ⟨Z,_,hA,hB⟩ := active
          obtain ⟨v,_,hv⟩ := centered aBig hA
          obtain ⟨w,_,hw⟩ := centered bBig hB
          have centers {Y : Finset (Fin 42)} (a : r.1 ∈ seed Y) (b : r.2 ∈ seed Y) : v∈Y ∧ w∈Y := by
            obtain ⟨i,hi,si⟩ := centered aBig a
            obtain ⟨j,hj,sj⟩ := centered bBig b
            exact ⟨unique aBig si hv ▸ hi,unique bBig sj hw ▸ hj⟩
          by_cases eq : v=w
          · subst w
            apply discard
            rintro Y _ s (old | ⟨ha,hb,sub⟩)
            · exact old
            · exact Or.inr ⟨v,(centers ha hb).1, sub.trans (Finset.union_subset hv hw)⟩
          · have full : ∀ Y, covers Y → T ∈ q.foldl grow (grow (seed Y) (star v,star w)) := by
              intro Y hY
              apply mon q _ _ _ (solved Y hY)
              rintro s (old | ⟨ha,hb,sub⟩)
              · exact Or.inl old
              · obtain ⟨vy,wy⟩ := centers ha hb
                exact Or.inr ⟨Or.inr ⟨v,vy,Finset.Subset.rfl⟩,
                  Or.inr ⟨w,wy,Finset.Subset.rfl⟩,
                  sub.trans (Finset.union_subset_union hv hw)⟩
            have bound := obstruction v w eq q T full
            omega
        · apply discard
          rintro Y hY s (old | ⟨ha,hb,_⟩)
          · exact old
          · exact (active ⟨Y,hY,ha,hb⟩).elim
  have compile :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (n : ℕ) (X : I → Fin n → Bool)
            (R : List (Finset ℕ × Finset ℕ)) (out : Finset ℕ),
          let ev (x : Fin n → Bool) :=
            let w := R.foldl (fun w r => w ++ [decide (∀ i ∈ r.1, w.getD i false = true) ||
              decide (∀ i ∈ r.2, w.getD i false = true)]) (List.ofFn x ++ [false])
            decide (∀ i ∈ out, w.getD i false = true)
          let grow (F : Set (Finset I)) (r : Finset I × Finset I) :=
            {s | s ∈ F ∨ r.1 ∈ F ∧ r.2 ∈ F ∧ s ⊆ r.1 ∪ r.2}
          (∀ i, ev (X i) = true) →
          ∃ Q : List (Finset I × Finset I), Q.length ≤ R.length ∧
            ∀ x, ev x = false → Finset.univ ∈ Q.foldl grow
              {s | s = ∅ ∨ ∃ v : Fin n, x v = false ∧ ∀ i ∈ s, X i v = true}
  := by
    intro I _ _ n X R out ev grow positives
    classical
    let term (w : List Bool) (a : Finset ℕ) := decide (∀ j ∈ a, w.getD j false = true)
    let run (Q : List (Finset ℕ × Finset ℕ)) (x : Fin n → Bool) :=
      Q.foldl (fun w r => w ++ [term w r.1 || term w r.2]) (List.ofFn x ++ [false])
    let wire (Q : List (Finset ℕ × Finset ℕ)) (j : ℕ) :=
      Finset.univ.filter (fun e : I => (run Q (X e)).getD j false = true)
    let seed (x : Fin n → Bool) : Set (Finset I) :=
      {s | s = ∅ ∨ ∃ v : Fin n, x v = false ∧ ∀ i ∈ s, X i v = true}
    have down (rs : List (Finset I × Finset I)) (F : Set (Finset I))
        (hd : ∀ a ∈ F, ∀ b : Finset I, b ⊆ a → b ∈ F) :
        ∀ a ∈ rs.foldl grow F, ∀ b : Finset I, b ⊆ a → b ∈ rs.foldl grow F := by
      induction rs generalizing F with
      | nil => exact hd
      | cons r q ih =>
        apply ih
        rintro a (old | ⟨ha,hb,sub⟩) b sb
        · exact Or.inl (hd _ old _ sb)
        · exact Or.inr ⟨ha,hb,sb.trans sub⟩
    have seedDown (x : Fin n → Bool) : ∀ a ∈ seed x, ∀ b : Finset I, b ⊆ a → b ∈ seed x := by
      rintro a (rfl | ⟨v,hv,h⟩) b sub
      · exact Or.inl (Finset.subset_empty.mp sub)
      · exact Or.inr ⟨v,hv,fun i hi => h i (sub hi)⟩
    have zero (x : Fin n → Bool) (q : List (Finset I × Finset I)) : ∅ ∈ q.foldl grow (seed x) := by
      have old (F : Set (Finset I)) (q : List (Finset I × Finset I)) : F ⊆ q.foldl grow F := by
        induction q generalizing F with
        | nil => exact fun _ h => h
        | cons r rs ih => exact fun _ h => ih (grow F r) (Or.inl h)
      exact old _ q (Or.inl rfl)
    have appendWire (Q : List (Finset ℕ × Finset ℕ)) (r : Finset ℕ × Finset ℕ) (x : Fin n → Bool) :
        run (Q++[r]) x = run Q x ++ [term (run Q x) r.1 || term (run Q x) r.2] := by simp [run,List.foldl_append]
    have length (Q : List (Finset ℕ × Finset ℕ)) (x : Fin n → Bool) : (run Q x).length = n+1+Q.length := by
      induction Q using List.reverseRecOn with
      | nil => simp [run]
      | append_singleton Q r ih => rw [appendWire]; simp [ih]; omega
    have read (w : List Bool) (b : Bool) (j : ℕ) : (w++[b]).getD j false =
        if j=w.length then b else w.getD j false := by
      rcases lt_trichotomy j w.length with h | h | h
      · simp [List.getD_eq_getElem?_getD,List.getElem?_append_left h,h.ne]
      · subst j; simp [List.getD_eq_getElem?_getD]
      · simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (show (w++[b]).length ≤ j by simp;omega),
          List.getElem?_eq_none h.le,h.ne']
    have sim (Q : List (Finset ℕ × Finset ℕ)) :
        ∃ rs : List (Finset I × Finset I), rs.length = Q.length ∧
        ∀ x j, (run Q x).getD j false = false → wire Q j ∈ rs.foldl grow (seed x) := by
      induction Q using List.reverseRecOn with
      | nil =>
        refine ⟨[],rfl,?_⟩
        intro x j h
        have base (z : Fin n → Bool) : (run [] z).getD j false =
            if h : j<n then z ⟨j,h⟩ else false := by
          by_cases hj : j<n
          · simp [run,List.getD_eq_getElem?_getD,List.getElem?_append_left (by simpa using hj :
              j < (List.ofFn z).length),hj]
          · by_cases hj' : j=n
            · subst j; simp [run,List.getD_eq_getElem?_getD]
            · have hlen : (List.ofFn z ++ [false]).length ≤ j := by simp; omega
              simp [run,List.getD_eq_getElem?_getD,List.getElem?_eq_none hlen,hj]
        by_cases hj : j<n
        · refine Or.inr ⟨⟨j,hj⟩,?_,?_⟩
          · rwa [base,dite_eq_left hj] at h
          · intro e he; have value := (Finset.mem_filter.mp he).2; rwa [base,dite_eq_left hj] at value
        · apply Or.inl
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro e he; have value := (Finset.mem_filter.mp he).2; rw [base,dite_eq_right hj] at value; contradiction
      | append_singleton Q r ih =>
        obtain ⟨rs,hlen,pre⟩ := ih
        let arg (a : Finset ℕ) := Finset.univ.filter (fun e : I => term (run Q (X e)) a = true)
        refine ⟨rs++[(arg r.1,arg r.2)],by simp [hlen],?_⟩
        intro x j hj
        simp only [List.foldl_append,List.foldl_cons,List.foldl_nil]
        have atWire (z : Fin n → Bool) : (run (Q++[r]) z).getD j false =
            if j=n+1+Q.length then term (run Q z) r.1 || term (run Q z) r.2 else (run Q z).getD j false := by
          rw [appendWire,read,length]
        rw [atWire] at hj
        by_cases idx : j=n+1+Q.length
        · simp only [ite_eq_left idx,Bool.or_eq_false_iff] at hj
          have argReady (a : Finset ℕ) (ha : term (run Q x) a = false) :
              arg a ∈ rs.foldl grow (seed x) := by
            have hn : ¬ ∀ k ∈ a, (run Q x).getD k false = true := of_decide_eq_false ha
            push Not at hn
            obtain ⟨k,hk,hkfalse⟩ := hn
            apply down rs (seed x) (seedDown x) (wire Q k) (pre x k (by simpa using hkfalse))
            intro e he
            have val : ∀ i ∈ a, (run Q (X e)).getD i false = true :=
              of_decide_eq_true (Finset.mem_filter.mp he).2
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,val _ hk⟩
          refine Or.inr ⟨argReady _ hj.1,argReady _ hj.2,?_⟩
          intro e he
          have value := (Finset.mem_filter.mp he).2
          rw [atWire,ite_eq_left idx] at value
          simpa [arg] using value
        · have prev := pre x j (by simpa [idx] using hj)
          apply Or.inl
          have same : wire (Q++[r]) j = wire Q j := by
            ext e
            simp only [wire,Finset.mem_filter,Finset.mem_univ,true_and]
            rw [atWire,ite_eq_right idx]
          rwa [same]
    obtain ⟨rs,len,sim'⟩ := sim R
    refine ⟨rs,len.le,?_⟩
    intro x hx
    have hn : ¬∀ j ∈ out, (run R x).getD j false = true := of_decide_eq_false hx
    push Not at hn
    obtain ⟨j,hj,bad⟩ := hn
    have sig := sim' x j (by simpa using bad)
    have all : wire R j = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro e
      have he : ∀ i ∈ out, (run R (X e)).getD i false = true := of_decide_eq_true (positives e)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he _ hj⟩
    rwa [← all]
  let X (e : I) (v : Fin 42) := decide (v = pt e ∨ v = ln e)
  have incid : ∀ p l : Fin 21, posted p l = true ↔ ∃ i : Fin 5, l = p + ![20,0,5,7,17] i := by
    decide +kernel
  have positives : ∀ e : I, eval (X e) = true :=
    fun e => pos e.1 _ ((incid _ _).mpr ⟨e.2,rfl⟩)
  obtain ⟨Q,len,cert⟩ := compile I 42 X R out positives
  have win : wins Q Finset.univ := by
    intro Z hZ
    let x (v : Fin 42) := decide (v ∉ Z)
    have hx : indep x := by
      intro p l hpl
      obtain ⟨i,rfl⟩ := (incid p l).mp hpl
      obtain ⟨v,hv,he⟩ := hZ (p,i)
      rcases (Finset.mem_filter.mp he).2 with h | h
      · exact Or.inl (by change decide (pt (p,i) ∉ Z) = false; exact decide_eq_false (not_not_intro (h.symm ▸ hv)))
      · exact Or.inr (by change decide (ln (p,i) ∉ Z) = false; exact decide_eq_false (not_not_intro (h.symm ▸ hv)))
    let ones (z : Fin 42 → Bool) := Finset.univ.filter fun v => z v = true
    let up := Finset.univ.filter fun z : Fin 42 → Bool => indep z ∧ ones x ⊆ ones z
    have xup : x ∈ up := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx,Finset.Subset.rfl⟩
    obtain ⟨y,yup,high⟩ := Finset.exists_max_image up (fun z => (ones z).card) ⟨x,xup⟩
    obtain ⟨yi,xy⟩ := (Finset.mem_filter.mp yup).2
    have yn : eval y = false := by
      apply neg y yi
      intro z zi yz
      have sub : ones y ⊆ ones z := fun v hv => Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, yz v (Finset.mem_filter.mp hv).2⟩
      have eq := Finset.eq_of_subset_of_card_le sub (high z (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,zi,xy.trans sub⟩))
      funext v
      have iff : z v = true ↔ y v = true := by
        simpa [ones] using (show v ∈ ones z ↔ v ∈ ones y by rw [eq])
      cases hz : z v <;> cases hy : y v
      · rfl
      · have no := iff.mpr hy
        simp [hz] at no
      · have no := iff.mp hz
        simp [hy] at no
      · rfl
    apply mon Q _ _ _ (cert y yn)
    rintro s (emp | ⟨v,hv,hs⟩)
    · exact Or.inl emp
    · have vZ : v ∈ Z := by
        by_contra hn
        have xv : v ∈ ones x := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [x,hn]⟩
        have yv := (Finset.mem_filter.mp (xy xv)).2
        simp [hv] at yv
      refine Or.inr ⟨v,vZ,?_⟩
      intro e he
      have h : v = pt e ∨ v = ln e := of_decide_eq_true (hs e he)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
  have size := game Q.length Q Finset.univ rfl win
  have hsize : (Finset.univ : Finset I).card = 105 := by decide
  rw [hsize] at size
  omega
