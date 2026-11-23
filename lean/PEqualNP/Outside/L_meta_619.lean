import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_619

def opsL (p : ℕ) (S : List ℕ) : List ℕ := S.flatMap (fun s => [p &&& s, p ||| s])

def addBits (l : List ℕ) (acc : ℕ) : ℕ := l.foldl (fun a v => a ||| (1 <<< v)) acc

def fresh : List ℕ → ℕ → List ℕ
  | [], _ => []
  | v :: l, seen => if seen.testBit v then fresh l seen else v :: fresh l (seen ||| (1 <<< v))

def orPack : ℕ := 179769313472279655784825371871634786684055947010586889823843161019800249899092506420881857535768475611440354061764121114905765102931035171412970511388217341376163738745051339457801394361292518430899342993111184336311432594510100520372354421365899689387611764646025354040599510002824985923437773071428846878720

def andPack : ℕ := 16908778031146387716180665223370243780169991614599422797221467094903426816429363826113244175351662983413183107997978614823663953903123051247262466967653183105912694442639091157236978773759188775433632403112340727698520300085798458694012758642233316186495276873759388498269743914078480357505925093861345745108181478862263839436640606122156408010688065147419984764430865357864546669166061079573131021374848944874204226376521977423998285264754688643987908235648781838300966876117621060723009663077358853462067193551270252227967523167080036869248471507857805761366594862255192989349679116738511130044336399197579191557961414147679297160283088408168067410442787643773676528868896753540838921151261594231578389018727365554522799814857269855341457903618833800565292871489746926431756391224781263485579311761470332785726775647476613723598184227556825181004941039023700510736466286569193399521737453337316716794547639029335545547791432969990894676677881295846625923294601102189404037007618237156523939191749055853745602852896511415650282806007411924727421198406915124549287580004418541990977028500305187069359589473166324551025657572295097987260577423793692748571277055585915803634304395943800748643056819217628822613099850340704196353842276724940698238820108379962691949767052028511572467174192353826115107866896492742189628008156639396388686988914071415253393474052328730198658703636025266172165031521031867838485693112282628656672306820139392908240857838549979102883016850937887887420630368269448909517359585215928116826313277180384382083253840084802770588895392307003829807999336595637500826971507883478916075839416077496507225381539115553499103604029503782552377383107324959512481878660101977912924732149324307388177781339560763083715624562322572697671897029787944242156392432693130858175848218045275162059456419977498711663265718996128206607531041941704789832395600560665455283568304833858204666584382954005396478749905304513636704076009201121719701241415406083019253692935359566763132741886349240508568967016696360452452501562521542219224112099365116022635936097830766601786694811906031669619803401414767842244321354261902082574708166514325447915024080846932265268397062347009397161574094166616699102357219419992720019812296811805615253949210317636495322406843317175279795386876697761192216032492321784159275156646792354081452337142663183308485210218953591094387015285095128463134613736905216216632927136741433985164665949394302628172750972140795151553937782404482543466628215571512956413953770098090480047328949765470362532019870130156558343883432912910208415219535173761871517809989473937174994794506440545714777870528935480320230424189243643221746385899021609180241251657660434609701372794524418287171662554183819216429976215097255738040893031452907359477815910887141019114720657258047566726944345330286102437700763392657419220045988750225379961400796733482748130100127438523893070658398280207950096018185066054361392093340713047981900658641168288911825393901695945452379798391656929010690152770629478188858064987974929593646820460381120338408345876870640308326276878699217130553841064524236268289004300418141261904192355030380487471621875867089830550660149286123858857985735856020361453915885465881882802364445465259483428330399112766896737400409476334484836391872589286875847893578985793986504211702871727678819563452146896979483868211881405325168286343674739453583476495133865753284139562666253043974156788826136836590456199350165920382066747334911937041496113097270530019313626670123448077349060343128727122874932168285813316560729535900603159626049591192825419236266405150223031297623335206599243032230134528119321019170140560745302774143386870788092311876315672415439145002495663224206138336981809565886229851613132849066908378614996261329994870759445743075910520776827648595945174762103676706755111590913938346168929758925177787746877153610268735063503553262259371491730316090067463018423627891911834670200308761252620576590320550622869578395570750049889790197299516858303567826339404560628250664378179540376349005388381646042371701754633088791211294631177558763184224972767205081797546002591649777495426379503298883153149010425644158967230971063450107384008799316613499165032883244920713125515918954245827728725154106955601479111714290301323670702469393906019914419798293416942866131040537722012137003485025155739184786635855582536488928510241379034748228320751886013389889505112851316371990276862994411212063292056646497629273503642699401506549690885701491613327551168708478185709890893775850627401452091027085790972886182743383308871678135100631145571431474331522735037190923438226115759416801999544485356452535881334459029699688502941053647323013540588614460737849145709737465934246715129617948011444882330347348427658742525743115301047730954110785818024903963595081868680348086013641712767587089687259016131818572502556138128858646710170448588702318965041372979242710849884877673212263086717002825358948873434208470379993532384560098488395871763038309614081185727573323223248010502684675463753981443581563623688018839432744287035462060490997469421701389219828136854860662805273040355860815348097036247311415405513271903406145325075329525504129206027977184345584412851784898920666867414003134051167293156280591875366407409087626594742820705256357998566910685494709838315162463757636669010782310066150081709128587223638299124831114100698856152357080542941569987357414847388433088690221552839091464222419083490988214284180298644049502080418034216923343398655473774044425469053613503051581365553598287070224232064890948027204027286468410690987496603795182661886761504253735948755981086776951131466479589339022235730090881110058973413445099795525779830812963720930691264948382747918087691681476079164993933524622401315613347149794280718284272162044712805034350571646469031743275709364453699716878193133513755357262576838135580052483770193060821551908536800605741450609912700536794335185887078381716804700602038468290764999060734110658928623581786242386821360794118161499868504292883049059975546107240758654863271423354336067018343093595089596878758063527074911964406093034208475769899097387649067238147059081359893423830507880958248722568178676573750750863576042805009532029931040177596234530311838127479905646376157419091903656325834181276551646014204901903179443353596326984770703373533113420771988440056968860068538098071260847179951223865908397773014390721175346540321862389200289569619150652387883347913961461001424134219293395007093010252741548068121399860982251745028368083415310983727975600943552348096621861997315342255891486761956086627408299039533713581287037505896408655918075274092217362181658449533807602031233024434446252993251528693329399601507354280592914346256897406459385189005345134974275514032467039050191133402404927065691466657813216940630065853590151469055803101750426340698109777431788304074628747719695636873437337954104476740001377303043980547185223255870883550412929371801026904663976444505724299433258648402031290294235201194781677991593162547122795554536414314928835371363310502191203921908794599580268074655915750068816623733902634026188672774988549463663336513730413607516903958445547160470092739715331228967730794001312171342596799952069437623521681097519160230152636620891602695282934258225659423747389882529109278552163796697938741412051841494572978329809730705745164296204069545103843985943262448470753656640506899699881886450656978385696180465407459826442762210629850335068830117327240869143157400959094298043263032436898827664025145178581645845632377313535178301380803033387101342775755087238758270343967392682959401567433570288210377132907911000581824964606245991146805964528853805340654573373070324919500537857747705733856807687634731588507709601286911837081318315758975622389895292498988828115926721152651031545493325829002976463555064396933554693256819669047223278176763851493228708585222400840358402786275903593052727616460963855374723412189364125408402732450795426715406395266012827749451193180939868820676335330660477945776035087704043858753211022902240638534590385922726082658912973558665771359888672823352443099743996711310739675000288227996861493730561828904318620593492162497909362051626041362016435868855732042625970665257367755221206047912378977033325472848162121008569341161983652927079937159696652116286136614438940815317969650238467346183347724698462622582253104951571393575846249440135920166948482198305417832505439185573725648244897778128497573661277549360419313985141901259357255327947130729252769083398437282308780221440028719987286875190566999290158759864085622608069199178276901057024412918942998421636291263677921827064400398708188785426753867901537701681510054345961527132345801420043687670964816334833182624185550460213914901146239695171607040338520028940866338747870393510431507701846048920648417708374174195016547154707806802298042562748037116310975532002260953949771969325779973131426492510977503615628888207628851359974877033517009923213047157706708550318201097730344040766735313200533846336624624963439928004669066302704760922875853413107659628765015310855098962052624995689791255469194908855291029351359555564260577521791362162546212026273151374121298710011094536996989312173121354887186391463724032101299272778450627426165617388751077040209834765677364339562547069279334710409243855416162022448394321749684702578153335319922071880698113778986462744059454232879723607306511077155115759916245224762178448257104818369391307565405756263494625380603988399622618040137555789436511492626320914220777612197824574053952754324720268161118825410461231322400045907819588742572077178710484472240799744

def gtab (v : ℕ) : ℕ :=
  if (v &&& 31) == v then (orPack >>> (32 * v)) &&& (2 ^ 32 - 1)
  else if (v &&& 31) == 31 then (andPack >>> (1024 * (v >>> 5))) &&& (2 ^ 1024 - 1)
  else 0

def node : ℕ → List ℕ → ℕ → ℕ → List ℕ → ℕ → ℕ → Bool
  | k, S, Sb, p, Dl, Db, Gb =>
    let N := opsL p S
    let D := addBits N Db
    if D.testBit 31 then true else
    match k with
    | 0 => (D &&& Gb) != 0
    | k + 1 =>
      ((Dl.filter (fun v => p < v && !(Sb.testBit v))) ++ fresh N (Db ||| Sb)).any
        (fun v => node k (S ++ [v]) (Sb ||| (1 <<< v)) v (Dl ++ fresh N Db) D (Gb ||| gtab v))

def S0 : List ℕ := [305, 579, 166, 332, 664, 0, 0, 1023]

def D0 : List ℕ := fresh (S0.flatMap (fun a => S0.flatMap (fun b => [a &&& b, a ||| b]))) 0

def G0 : ℕ := S0.foldl (fun g c => g ||| gtab c) 0

def roots : List ℕ := [1, 32, 381, 494]

def P0 : List ℕ := [305, 579, 166, 332, 664]

def rootRun (v : ℕ) : Bool :=
  node 3 (P0 ++ [v]) (addBits (S0 ++ [v]) 0) v D0 (addBits D0 0) (G0 ||| gtab v)

/-! ## Derivations over 10-bit vectors -/

def dv (S : List ℕ) (v : ℕ) : Prop := ∃ a ∈ S, ∃ b ∈ S, v = a &&& b ∨ v = a ||| b

def NS : List ℕ → List ℕ → Prop
  | _, [] => True
  | S, v :: l => v ∉ S ∧ dv S v ∧ NS (S ++ [v]) l

def VC : List ℕ → List ℕ → ℕ → Prop
  | _, [], _ => True
  | S, v :: l, k => (v ∈ S ∧ VC (S ++ [v]) l k) ∨ (0 < k ∧ dv S v ∧ VC (S ++ [v]) l (k - 1))

theorem dv_mono {S S' : List ℕ} {v : ℕ} (h : ∀ x ∈ S, x ∈ S') (hv : dv S v) : dv S' v := by
  obtain ⟨a, ha, b, hb, e⟩ := hv
  exact ⟨a, h a ha, b, h b hb, e⟩

theorem NS_congr : ∀ (l S S' : List ℕ), (∀ x, x ∈ S ↔ x ∈ S') → NS S l → NS S' l
  | [], _, _, _, _ => trivial
  | v :: l, S, S', h, ⟨h1, h2, h3⟩ => by
    refine ⟨fun hv => h1 ((h v).2 hv), dv_mono (fun x hx => (h x).1 hx) h2, ?_⟩
    refine NS_congr l (S ++ [v]) (S' ++ [v]) ?_ h3
    intro x
    simp only [List.mem_append, List.mem_singleton, h x]

theorem VC_to_NS : ∀ (l S : List ℕ) (k : ℕ), VC S l k →
    ∃ ns, NS S ns ∧ ns.length ≤ k ∧ ∀ x, x ∈ S ++ l → x ∈ S ++ ns
  | [], S, k, _ => ⟨[], trivial, by simp, fun x hx => by simpa using hx⟩
  | v :: l, S, k, h => by
    have key : ∀ k', k' ≤ k → v ∈ S → VC (S ++ [v]) l k' →
        ∃ ns, NS S ns ∧ ns.length ≤ k ∧ ∀ x, x ∈ S ++ v :: l → x ∈ S ++ ns := by
      intro k' hk hv hl
      obtain ⟨ns, h1, h2, h3⟩ := VC_to_NS l (S ++ [v]) k' hl
      have eqv : ∀ x, x ∈ S ++ [v] ↔ x ∈ S := by
        intro x; simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro (hx | rfl); exacts [hx, hv]
        · intro hx; exact Or.inl hx
      refine ⟨ns, NS_congr ns _ _ eqv h1, by omega, ?_⟩
      intro x hx
      have hx' : x ∈ S ++ [v] ++ l := by simpa using hx
      have := h3 x hx'
      simp only [List.mem_append, List.mem_singleton] at this ⊢
      rcases this with (h | rfl) | h
      · exact Or.inl h
      · exact Or.inl hv
      · exact Or.inr h
    rcases h with ⟨hv, hl⟩ | ⟨hk, hd, hl⟩
    · exact key k le_rfl hv hl
    · by_cases hv : v ∈ S
      · exact key (k - 1) (by omega) hv hl
      · obtain ⟨ns, h1, h2, h3⟩ := VC_to_NS l (S ++ [v]) (k - 1) hl
        refine ⟨v :: ns, ⟨hv, hd, h1⟩, by simp; omega, ?_⟩
        intro x hx
        have hx' : x ∈ S ++ [v] ++ l := by simpa using hx
        simpa using h3 x hx'

theorem NS_trunc : ∀ (ns S : List ℕ) (t : ℕ), NS S ns → t ∈ ns →
    ∃ ns', NS S ns' ∧ ns'.length ≤ ns.length ∧ ns'.getLast? = some t
  | [], _, _, _, h => by simp at h
  | v :: l, S, t, ⟨h1, h2, h3⟩, ht => by
    by_cases hvt : v = t
    · subst hvt
      exact ⟨[v], ⟨h1, h2, trivial⟩, by simp, by simp⟩
    · have ht' : t ∈ l := by
        rcases List.mem_cons.mp ht with h | h
        · exact absurd h.symm hvt
        · exact h
      obtain ⟨ns', a1, a2, a3⟩ := NS_trunc l (S ++ [v]) t h3 ht'
      have hne : ns' ≠ [] := by rintro rfl; simp at a3
      refine ⟨v :: ns', ⟨h1, h2, a1⟩, by simp; omega, ?_⟩
      rw [List.getLast?_cons, a3]
      simp

theorem dv_lt {S : List ℕ} {v : ℕ} (hS : ∀ x ∈ S, x < 1024) (h : dv S v) : v < 1024 := by
  obtain ⟨a, ha, b, hb, e | e⟩ := h <;> subst e
  · exact Nat.and_lt_two_pow a (n := 10) (hS b hb)
  · exact Nat.or_lt_two_pow (n := 10) (hS a ha) (hS b hb)

theorem NS_lt : ∀ (ns S : List ℕ), (∀ x ∈ S, x < 1024) → NS S ns → ∀ x ∈ S ++ ns, x < 1024
  | [], S, hS, _ => by simpa using hS
  | v :: l, S, hS, ⟨_, h2, h3⟩ => by
    have hv := dv_lt hS h2
    have := NS_lt l (S ++ [v]) (by
      intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hS x hx
      · exact hv) h3
    intro x hx
    exact this x (by simpa using hx)

/-! ## Bit sets -/

theorem tb_or_shift (a x v : ℕ) : (a ||| (1 <<< x)).testBit v = (a.testBit v || decide (x = v)) := by
  rw [Nat.testBit_lor, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]

theorem addBits_tb : ∀ (l : List ℕ) (acc v : ℕ), (addBits l acc).testBit v = true ↔ acc.testBit v = true ∨ v ∈ l
  | [], acc, v => by simp [addBits]
  | x :: l, acc, v => by
    have : addBits (x :: l) acc = addBits l (acc ||| (1 <<< x)) := rfl
    rw [this, addBits_tb l, tb_or_shift]
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro ((h | rfl) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr h)
    · rintro (h | rfl | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr h

theorem fresh_mem : ∀ (l : List ℕ) (seen v : ℕ), v ∈ fresh l seen ↔ v ∈ l ∧ seen.testBit v = false
  | [], seen, v => by simp [fresh]
  | x :: l, seen, v => by
    unfold fresh
    split
    · rename_i hx
      rw [fresh_mem l]
      simp only [List.mem_cons]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨Or.inr h1, h2⟩
      · rintro ⟨rfl | h1, h2⟩
        · rw [hx] at h2; exact absurd h2 (by simp)
        · exact ⟨h1, h2⟩
    · rename_i hx
      simp only [List.mem_cons, fresh_mem l, tb_or_shift]
      constructor
      · rintro (rfl | ⟨h1, h2⟩)
        · simpa using hx
        · simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h2
          exact ⟨Or.inr h1, h2.1⟩
      · rintro ⟨rfl | h1, h2⟩
        · exact Or.inl rfl
        · by_cases hvx : v = x
          · exact Or.inl hvx
          · refine Or.inr ⟨h1, ?_⟩
            simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
            exact ⟨h2, fun e => hvx e.symm⟩

theorem mem_opsL {p v : ℕ} {S : List ℕ} : v ∈ opsL p S ↔ ∃ s ∈ S, v = p &&& s ∨ v = p ||| s := by
  simp only [opsL, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]

theorem gtab_sound (c x : ℕ) (hc : c < 1024) (hc31 : c ≠ 31) (hx : x < 1024)
    (h : x &&& c = 31 ∨ x ||| c = 31) : (gtab c).testBit x = true := by
  have lemB : ∀ c, c < 32 → ∀ s, s < 32 → s &&& c = 0 → c ≠ 0 →
      (gtab (31 + 32 * c)).testBit (31 + 32 * s) = true := by decide +kernel
  have lemA : ∀ c, c < 31 → ∀ x, x < 32 → x ||| c = 31 → (gtab c).testBit x = true := by
    decide +kernel
  rcases h with h | h
  · -- and case: c contains 31
    have hc1 : c &&& 31 = 31 := by
      apply Nat.eq_of_testBit_eq; intro i
      have := congrArg (fun n => n.testBit i) h
      simp only [Nat.testBit_land] at this ⊢
      rw [← this]; cases x.testBit i <;> cases c.testBit i <;> rfl
    have hcm : c % 32 = 31 := by
      have := Nat.and_two_pow_sub_one_eq_mod c 5
      norm_num at this
      omega
    have hx1 : x &&& 31 = 31 := by
      have e1 : (x &&& c) &&& 31 = 31 := by rw [h]; rfl
      rw [Nat.land_assoc, hc1] at e1
      exact e1
    have hxm : x % 32 = 31 := by
      have := Nat.and_two_pow_sub_one_eq_mod x 5
      norm_num at this
      omega
    have hs : (x >>> 5) &&& (c >>> 5) = 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      have := congrArg (fun n => n.testBit (i + 5)) h
      simp only [Nat.testBit_land] at this
      simp only [Nat.testBit_land, Nat.testBit_shiftRight, Nat.zero_testBit]
      rw [show 5 + i = i + 5 by omega, this]
      apply Nat.testBit_eq_false_of_lt
      calc 31 < 2 ^ 5 := by norm_num
        _ ≤ 2 ^ (i + 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have ex : x = 31 + 32 * (x >>> 5) := by
      rw [Nat.shiftRight_eq_div_pow]; norm_num; omega
    have ec : c = 31 + 32 * (c >>> 5) := by
      rw [Nat.shiftRight_eq_div_pow]; norm_num; omega
    have hc0 : c >>> 5 ≠ 0 := by
      intro h0; rw [h0] at ec; exact hc31 (by omega)
    rw [ex, ec]
    apply lemB
    · rw [Nat.shiftRight_eq_div_pow]; norm_num; omega
    · rw [Nat.shiftRight_eq_div_pow]; norm_num; omega
    · exact hs
    · exact hc0
  · have hx32 : x ≤ 31 := h ▸ Nat.left_le_or
    have hc32 : c ≤ 31 := h ▸ Nat.right_le_or
    exact lemA c (by omega) x (by omega) h

/-! ## Symmetry -/

def piV (bs : List Bool) : ℕ := bs.foldr (fun b acc => Nat.bit b acc) 0

theorem piV_tb : ∀ (bs : List Bool) (i : ℕ), (piV bs).testBit i = bs.getD i false
  | [], i => by simp [piV]
  | b :: bs, 0 => by simp [piV]
  | b :: bs, i + 1 => by
    have : piV (b :: bs) = Nat.bit b (piV bs) := rfl
    rw [this, Nat.testBit_bit_succ, piV_tb bs i]
    simp

def sigma (g : List ℕ) (v : ℕ) : ℕ := piV ((List.range 10).map fun i => v.testBit (g.getD i 0))

theorem sigma_tb (g : List ℕ) (v i : ℕ) :
    (sigma g v).testBit i = (decide (i < 10) && v.testBit (g.getD i 0)) := by
  rw [sigma, piV_tb]
  by_cases hi : i < 10
  · simp [hi, List.getD_eq_getElem?_getD]
  · simp [hi, List.getD_eq_getElem?_getD]

theorem sigma_land (g : List ℕ) (a b : ℕ) : sigma g (a &&& b) = sigma g a &&& sigma g b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [sigma_tb, Nat.testBit_land]
  cases decide (i < 10) <;> simp

theorem sigma_lor (g : List ℕ) (a b : ℕ) : sigma g (a ||| b) = sigma g a ||| sigma g b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [sigma_tb, Nat.testBit_lor]
  cases decide (i < 10) <;> simp

theorem sigma_inv (g h : List ℕ) (hgh : ∀ i < 10, h.getD i 0 < 10 ∧ g.getD (h.getD i 0) 0 = i)
    (v : ℕ) (hv : v < 1024) : sigma h (sigma g v) = v := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [sigma_tb, sigma_tb]
  by_cases hi : i < 10
  · obtain ⟨h1, h2⟩ := hgh i hi
    rw [h2]; simp only [hi, h1, decide_true, Bool.true_and]
  · have : v.testBit i = false := by
      apply Nat.testBit_eq_false_of_lt
      calc v < 2 ^ 10 := by norm_num; exact hv
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp [hi, this]

def permPairs : List (List ℕ × List ℕ) :=
  [([0,1,2,3,4,5,6,7,8,9], [0,1,2,3,4,5,6,7,8,9]),
  ([4,0,1,2,3,9,5,6,7,8], [1,2,3,4,0,6,7,8,9,5]),
  ([3,4,0,1,2,8,9,5,6,7], [2,3,4,0,1,7,8,9,5,6]),
  ([2,3,4,0,1,7,8,9,5,6], [3,4,0,1,2,8,9,5,6,7]),
  ([1,2,3,4,0,6,7,8,9,5], [4,0,1,2,3,9,5,6,7,8]),
  ([4,3,2,1,0,8,7,6,5,9], [4,3,2,1,0,8,7,6,5,9]),
  ([0,4,3,2,1,9,8,7,6,5], [0,4,3,2,1,9,8,7,6,5]),
  ([1,0,4,3,2,5,9,8,7,6], [1,0,4,3,2,5,9,8,7,6]),
  ([2,1,0,4,3,6,5,9,8,7], [2,1,0,4,3,6,5,9,8,7]),
  ([3,2,1,0,4,7,6,5,9,8], [3,2,1,0,4,7,6,5,9,8])]

def perms : List (List ℕ) := permPairs.map Prod.fst

def permOKb (g h : List ℕ) : Bool :=
  ((List.range 10).all fun i => decide (h.getD i 0 < 10) && g.getD (h.getD i 0) 0 == i) &&
  S0.all (fun s => S0.contains (sigma g s)) &&
  S0.all (fun s => S0.any (fun s' => sigma g s' == s)) && sigma g 31 == 31

theorem permOK_all : ∀ gh ∈ permPairs, permOKb gh.1 gh.2 = true := by decide +kernel

theorem perm_facts {g : List ℕ} (hg : g ∈ perms) : ∃ h : List ℕ,
    (∀ i < 10, h.getD i 0 < 10 ∧ g.getD (h.getD i 0) 0 = i) ∧
    (∀ s ∈ S0, sigma g s ∈ S0) ∧ (∀ s ∈ S0, ∃ s' ∈ S0, sigma g s' = s) ∧ sigma g 31 = 31 := by
  obtain ⟨⟨g', h⟩, hmem, rfl⟩ := List.mem_map.mp hg
  have := permOK_all _ hmem
  simp only [permOKb, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq, List.contains_iff_mem, List.any_eq_true] at this
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := this
  exact ⟨h, fun i hi => h1 i hi, h2, h3, h4⟩

theorem S0_lt : ∀ x ∈ S0, x < 1024 := by decide

theorem dv_sigma (g : List ℕ) {S : List ℕ} {v : ℕ} (h : dv S v) : dv (S.map (sigma g)) (sigma g v) := by
  obtain ⟨a, ha, b, hb, e | e⟩ := h <;> subst e
  · exact ⟨sigma g a, List.mem_map_of_mem ha, sigma g b, List.mem_map_of_mem hb, Or.inl (sigma_land g a b)⟩
  · exact ⟨sigma g a, List.mem_map_of_mem ha, sigma g b, List.mem_map_of_mem hb, Or.inr (sigma_lor g a b)⟩

theorem NS_sigma (g h : List ℕ) (hgh : ∀ i < 10, h.getD i 0 < 10 ∧ g.getD (h.getD i 0) 0 = i) :
    ∀ (ns S : List ℕ), (∀ x ∈ S, x < 1024) → NS S ns → NS (S.map (sigma g)) (ns.map (sigma g))
  | [], _, _, _ => trivial
  | v :: l, S, hS, ⟨h1, h2, h3⟩ => by
    have hv := dv_lt hS h2
    refine ⟨?_, dv_sigma g h2, ?_⟩
    · intro hm
      obtain ⟨s, hs, e⟩ := List.mem_map.mp hm
      have : s = v := by
        rw [← sigma_inv g h hgh s (hS s hs), e, sigma_inv g h hgh v hv]
      exact h1 (this ▸ hs)
    · have := NS_sigma g h hgh l (S ++ [v]) (by
        intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hS x hx
        · exact hv) h3
      simpa using this

/-! ## Canonical derivations -/

def Canon (ns : List ℕ) : Prop :=
  (∀ A a b B, ns = A ++ a :: b :: B → B ≠ [] → dv (S0 ++ A) b → a < b) ∧
  (∀ v, ns.head? = some v → ∀ g ∈ perms, v ≤ sigma g v)

def Gd (ns : List ℕ) : Prop := NS S0 ns ∧ ns.length ≤ 6 ∧ ns.getLast? = some 31

def phiF : ℕ → List ℕ → ℕ
  | _, [] => 0
  | o, x :: l => o * x + phiF (o + 1) l

def mu (ns : List ℕ) : ℕ := (1024 - ns.headD 0) * 2 ^ 40 + phiF 0 ns

theorem phiF_le : ∀ (l : List ℕ) (o : ℕ), o + l.length ≤ 6 → (∀ x ∈ l, x < 1024) →
    phiF o l ≤ l.length * 6144
  | [], _, _, _ => by simp [phiF]
  | x :: l, o, h1, h2 => by
    have ih := phiF_le l (o + 1) (by simp at h1; omega) (fun y hy => h2 y (List.mem_cons_of_mem _ hy))
    have hx := h2 x (List.mem_cons_self ..)
    have ho : o ≤ 6 := by simp at h1; omega
    have : o * x ≤ 6 * 1024 := Nat.mul_le_mul ho (by omega)
    simp only [phiF, List.length_cons]
    nlinarith

theorem phiF_append : ∀ (A B : List ℕ) (o : ℕ), phiF o (A ++ B) = phiF o A + phiF (o + A.length) B
  | [], B, o => by simp [phiF]
  | x :: A, B, o => by
    simp only [List.cons_append, phiF, phiF_append A B (o + 1), List.length_cons]
    rw [show o + 1 + A.length = o + (A.length + 1) by omega]
    ring

theorem NS_append : ∀ (A B S : List ℕ), NS S (A ++ B) ↔ NS S A ∧ NS (S ++ A) B
  | [], B, S => by simp [NS]
  | x :: A, B, S => by
    simp only [List.cons_append, NS, NS_append A B (S ++ [x])]
    rw [show S ++ [x] ++ A = S ++ x :: A by simp]
    tauto

theorem NS_swap (S A B : List ℕ) (a b : ℕ) (h : NS S (A ++ a :: b :: B)) (hb : dv (S ++ A) b) :
    NS S (A ++ b :: a :: B) := by
  rw [NS_append] at h ⊢
  refine ⟨h.1, ?_⟩
  obtain ⟨_, ha1, ha2, hb1, _, hB⟩ := h
  have hne : a ≠ b := by intro e; apply hb1; simp [e]
  refine ⟨fun hm => hb1 (List.mem_append_left _ hm), hb, ?_, dv_mono (fun x hx => List.mem_append_left _ hx) ha2, ?_⟩
  · intro hm
    simp only [List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | hm
    · exact ha1 (List.mem_append.mpr hm)
    · exact hne hm
  · apply NS_congr B _ _ _ hB
    intro x; simp only [List.mem_append, List.mem_singleton]; tauto

def MB : ℕ := 1025 * 2 ^ 40

theorem Gd_lt {ns : List ℕ} (h : Gd ns) : ∀ x ∈ ns, x < 1024 :=
  fun x hx => NS_lt ns S0 S0_lt h.1 x (List.mem_append_right _ hx)

theorem phi_small {ns : List ℕ} (h : Gd ns) : phiF 0 ns < 2 ^ 40 := by
  have := phiF_le ns 0 (by have := h.2.1; omega) (Gd_lt h)
  have h6 := h.2.1
  have : ns.length * 6144 ≤ 6 * 6144 := Nat.mul_le_mul_right _ h6
  norm_num at *; omega

theorem mu_lt {ns : List ℕ} (h : Gd ns) : mu ns < MB := by
  have := phi_small h
  unfold mu MB
  have : (1024 - ns.headD 0) * 2 ^ 40 ≤ 1024 * 2 ^ 40 := Nat.mul_le_mul_right _ (by omega)
  norm_num at *; omega

theorem getLast_swap (A B : List ℕ) (a b : ℕ) (hB : B ≠ []) :
    (A ++ b :: a :: B).getLast? = (A ++ a :: b :: B).getLast? := by
  rw [show A ++ b :: a :: B = (A ++ [b, a]) ++ B by simp,
      show A ++ a :: b :: B = (A ++ [a, b]) ++ B by simp]
  rw [List.getLast?_append, List.getLast?_append]
  obtain ⟨x, B', rfl⟩ := List.exists_cons_of_ne_nil hB
  simp [List.getLast?_cons]

theorem improve {ns : List ℕ} (hg : Gd ns) (hc : ¬ Canon ns) : ∃ ns2, Gd ns2 ∧ mu ns < mu ns2 := by
  have hlt := Gd_lt hg
  simp only [Canon, not_and_or, not_forall] at hc
  rcases hc with ⟨A, a, b, B, he, hB, hd, hab⟩ | ⟨v, hv, g, hg', hle⟩
  · subst he
    have hnsw := NS_swap S0 A B a b hg.1 hd
    have hg2 : Gd (A ++ b :: a :: B) := ⟨hnsw, by have := hg.2.1; simp at this ⊢; omega,
      by rw [getLast_swap A B a b hB]; exact hg.2.2⟩
    refine ⟨_, hg2, ?_⟩
    have hns := hg.1
    rw [NS_append] at hns
    obtain ⟨_, _, _, hb1, _, _⟩ := hns
    have hne : b ≠ a := by intro e; apply hb1; simp [e]
    have hba : b < a := by omega
    have ha : a < 1024 := hlt a (by simp)
    have p1 := phi_small hg
    have p2 := phi_small hg2
    unfold mu
    cases A with
    | nil =>
      simp only [List.nil_append, List.headD_cons] at p1 p2 ⊢
      have : (1024 - a) * 2 ^ 40 + 2 ^ 40 ≤ (1024 - b) * 2 ^ 40 := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
      omega
    | cons x A' =>
      simp only [List.cons_append, List.headD_cons]
      rw [show x :: (A' ++ b :: a :: B) = (x :: A') ++ b :: a :: B by simp,
          show x :: (A' ++ a :: b :: B) = (x :: A') ++ a :: b :: B by simp,
          phiF_append, phiF_append]
      have e1 : phiF (0 + (x :: A').length) (b :: a :: B) + b
          = phiF (0 + (x :: A').length) (a :: b :: B) + a := by
        simp only [phiF]; ring
      omega
  · obtain ⟨h, hgh, _, hS0b, h31⟩ := perm_facts hg'
    have hS0a : ∀ s ∈ S0, sigma g s ∈ S0 := (perm_facts hg').choose_spec.2.1
    have hmap : ∀ x, x ∈ S0.map (sigma g) ↔ x ∈ S0 := by
      intro x; constructor
      · intro hx; obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx; exact hS0a s hs
      · intro hx; obtain ⟨s, hs, e⟩ := hS0b x hx; exact List.mem_map.mpr ⟨s, hs, e⟩
    have hns2 := NS_congr _ _ _ hmap (NS_sigma g h hgh ns S0 S0_lt hg.1)
    have hg2 : Gd (ns.map (sigma g)) := ⟨hns2, by simpa using hg.2.1, by
      rw [List.getLast?_map, hg.2.2]; simp [h31]⟩
    refine ⟨_, hg2, ?_⟩
    have p1 := phi_small hg
    have p2 := phi_small hg2
    obtain ⟨y, l, rfl⟩ : ∃ y l, ns = y :: l := by
      cases ns with
      | nil => simp at hv
      | cons y l => exact ⟨y, l, rfl⟩
    simp only [List.head?_cons, Option.some.injEq] at hv
    subst hv
    have hy : y < 1024 := hlt y (by simp)
    unfold mu
    simp only [List.map_cons, List.headD_cons] at p2 ⊢
    have : (1024 - y) * 2 ^ 40 + 2 ^ 40 ≤ (1024 - sigma g y) * 2 ^ 40 := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    omega

theorem canon_exists : ∀ n ns, Gd ns → MB - mu ns = n → ∃ ns', Gd ns' ∧ Canon ns' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ns hg hn
    by_cases hc : Canon ns
    · exact ⟨ns, hg, hc⟩
    · obtain ⟨ns2, hg2, hm⟩ := improve hg hc
      have h1 := mu_lt hg
      have h2 := mu_lt hg2
      exact ih (MB - mu ns2) (by omega) ns2 hg2 rfl

/-! ## Soundness of the search -/

theorem land_1023 {p : ℕ} (hp : p < 1024) : p &&& 1023 = p := by
  have := Nat.and_two_pow_sub_one_eq_mod p 10
  norm_num at this; rw [this]; omega

theorem lor_1023 {p : ℕ} (hp : p < 1024) : p ||| 1023 = 1023 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_lor, show (1023 : ℕ) = 2 ^ 10 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 10
  · simp [hi]
  · have : p.testBit i = false := by
      apply Nat.testBit_eq_false_of_lt
      calc p < 2 ^ 10 := by norm_num; exact hp
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp [hi, this]

theorem D_props (A Sop : List ℕ) (p : ℕ) (Db : ℕ) (hp : p < 1024)
    (hS1 : ∀ x ∈ Sop, x ∈ S0 ++ A ++ [p]) (hS2 : ∀ x ∈ S0 ++ A ++ [p], x ∈ Sop ∨ x = 0 ∨ x = 1023)
    (hD1 : ∀ v, Db.testBit v = true → dv (S0 ++ A) v)
    (hD2 : ∀ v, dv (S0 ++ A) v → v ∉ S0 ++ A → Db.testBit v = true) :
    (∀ v, (addBits (opsL p Sop) Db).testBit v = true → dv (S0 ++ A ++ [p]) v) ∧
    (∀ v, dv (S0 ++ A ++ [p]) v → ¬ dv (S0 ++ A) v → v ∉ S0 ++ A ++ [p] → v ∈ opsL p Sop) ∧
    (∀ v, dv (S0 ++ A ++ [p]) v → v ∉ S0 ++ A ++ [p] → (addBits (opsL p Sop) Db).testBit v = true) := by
  have hpS : p ∈ S0 ++ A ++ [p] := by simp
  have h0S : (0 : ℕ) ∈ S0 ++ A ++ [p] := List.mem_append_left _ (List.mem_append_left _ (by decide))
  have h1S : (1023 : ℕ) ∈ S0 ++ A ++ [p] := List.mem_append_left _ (List.mem_append_left _ (by decide))
  have P3 : ∀ v, dv (S0 ++ A ++ [p]) v → ¬ dv (S0 ++ A) v → v ∉ S0 ++ A ++ [p] → v ∈ opsL p Sop := by
    intro v hv hnd hvS
    obtain ⟨a, ha, b, hb, e⟩ := hv
    have key : ∀ s ∈ S0 ++ A ++ [p], (v = p &&& s ∨ v = p ||| s) → v ∈ opsL p Sop := by
      intro s hs e'
      rcases hS2 s hs with hs' | rfl | rfl
      · exact mem_opsL.mpr ⟨s, hs', e'⟩
      · exfalso; rcases e' with rfl | rfl
        · exact hvS (by simpa using h0S)
        · exact hvS (by simpa using hpS)
      · exfalso; rcases e' with rfl | rfl
        · exact hvS (by rw [land_1023 hp]; exact hpS)
        · exact hvS (by rw [lor_1023 hp]; exact h1S)
    have ha' : a ∈ S0 ++ A ∨ a = p := by
      rcases List.mem_append.mp ha with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_singleton.mp h)
    have hb' : b ∈ S0 ++ A ∨ b = p := by
      rcases List.mem_append.mp hb with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_singleton.mp h)
    rcases ha' with ha' | rfl
    · rcases hb' with hb' | rfl
      · exact absurd ⟨a, ha', b, hb', e⟩ hnd
      · apply key a ha
        rcases e with e | e
        · exact Or.inl (by rw [e, Nat.land_comm])
        · exact Or.inr (by rw [e, Nat.lor_comm])
    · exact key b hb e
  refine ⟨?_, P3, ?_⟩
  · intro v hv
    rcases (addBits_tb _ _ _).mp hv with h | h
    · exact dv_mono (fun x hx => List.mem_append_left _ hx) (hD1 v h)
    · obtain ⟨s, hs, e⟩ := mem_opsL.mp h
      exact ⟨p, hpS, s, hS1 s hs, e⟩
  · intro v hv hvS
    by_cases hd : dv (S0 ++ A) v
    · exact (addBits_tb _ _ _).mpr (Or.inl (hD2 v hd (fun h => hvS (List.mem_append_left _ h))))
    · exact (addBits_tb _ _ _).mpr (Or.inr (P3 v hv hd hvS))

theorem node_sound : ∀ (k : ℕ) (A : List ℕ) (p : ℕ) (rest Sop : List ℕ) (Sb : ℕ) (Dl : List ℕ) (Db Gb : ℕ),
    Gd (A ++ p :: rest) → Canon (A ++ p :: rest) → rest ≠ [] → A.length + 1 + k = 4 →
    (∀ x ∈ Sop, x ∈ S0 ++ A ++ [p]) → (∀ x ∈ S0 ++ A ++ [p], x ∈ Sop ∨ x = 0 ∨ x = 1023) →
    (∀ v, Sb.testBit v = true ↔ v ∈ S0 ++ A ++ [p]) →
    (∀ v, dv (S0 ++ A) v → v ∉ S0 ++ A → v ∈ Dl) →
    (∀ v, Db.testBit v = true → dv (S0 ++ A) v) →
    (∀ v, dv (S0 ++ A) v → v ∉ S0 ++ A → Db.testBit v = true) →
    (∀ x c, c ∈ S0 ++ A ++ [p] → c ≠ 31 → x < 1024 → (x &&& c = 31 ∨ x ||| c = 31) → Gb.testBit x = true) →
    node k Sop Sb p Dl Db Gb = true := by
  intro k
  induction k with
  | zero =>
    intro A p rest Sop Sb Dl Db Gb hg hc hr hlen hS1 hS2 hSb hDl hD1 hD2 hG
    have hlt := Gd_lt hg
    have hp : p < 1024 := hlt p (by simp)
    obtain ⟨P1, _, P2⟩ := D_props A Sop p Db hp hS1 hS2 hD1 hD2
    obtain ⟨x, rest', rfl⟩ := List.exists_cons_of_ne_nil hr
    have hns := hg.1
    rw [show A ++ p :: x :: rest' = (A ++ [p]) ++ x :: rest' by simp, NS_append] at hns
    obtain ⟨_, hx1, hx2, hx3⟩ := hns
    rw [show S0 ++ (A ++ [p]) = S0 ++ A ++ [p] by simp] at hx1 hx2 hx3
    unfold node
    simp only []
    split
    · rfl
    · rename_i h31
      have hx31 : x ≠ 31 := by rintro rfl; exact h31 (P2 31 hx2 hx1)
      have hlen6 := hg.2.1
      simp only [List.length_append, List.length_cons] at hlen6
      have hl : rest'.length ≤ 1 := by omega
      have hlast := hg.2.2
      match rest', hl, hx3, hlast with
      | [], _, _, hlast => simp at hlast; exact absurd hlast hx31
      | [y], _, hx3, hlast =>
        simp at hlast
        subst hlast
        obtain ⟨h31n, ⟨a, ha, b, hb, e⟩, _⟩ := hx3
        have hxD : (addBits (opsL p Sop) Db).testBit x = true := P2 x hx2 hx1
        have hxlt : x < 1024 := hlt x (by simp)
        have fin : Gb.testBit x = true → ((addBits (opsL p Sop) Db &&& Gb) != 0) = true := by
          intro hG'
          have : (addBits (opsL p Sop) Db &&& Gb).testBit x = true := by
            rw [Nat.testBit_land, hxD, hG']; rfl
          simp only [bne_iff_ne, ne_eq]
          intro h0; rw [h0, Nat.zero_testBit] at this; exact absurd this (by simp)
        have ha' : a ∈ S0 ++ A ++ [p] ∨ a = x := by
          rcases List.mem_append.mp ha with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_singleton.mp h)
        have hb' : b ∈ S0 ++ A ++ [p] ∨ b = x := by
          rcases List.mem_append.mp hb with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_singleton.mp h)
        rcases ha' with ha' | hax <;> rcases hb' with hb' | hbx
        · exact absurd (P2 31 ⟨a, ha', b, hb', e⟩ (fun h => h31n (List.mem_append_left _ h))) h31
        · rw [hbx] at e
          apply fin; apply hG x a ha'
          · intro e'; rw [e'] at ha'; exact h31n (List.mem_append_left _ ha')
          · exact hxlt
          · rcases e with e | e
            · exact Or.inl (by rw [Nat.land_comm]; exact e.symm)
            · exact Or.inr (by rw [Nat.lor_comm]; exact e.symm)
        · rw [hax] at e
          apply fin; apply hG x b hb'
          · intro e'; rw [e'] at hb'; exact h31n (List.mem_append_left _ hb')
          · exact hxlt
          · rcases e with e | e
            · exact Or.inl e.symm
            · exact Or.inr e.symm
        · exfalso; apply hx31
          rw [hax, hbx] at e
          rcases e with e | e
          · rw [e, Nat.and_self]
          · rw [e, Nat.or_self]
      | _ :: _ :: _, hl, _, _ => simp at hl
  | succ k ih =>
    intro A p rest Sop Sb Dl Db Gb hg hc hr hlen hS1 hS2 hSb hDl hD1 hD2 hG
    have hlt := Gd_lt hg
    have hp : p < 1024 := hlt p (by simp)
    obtain ⟨P1, P3, P2⟩ := D_props A Sop p Db hp hS1 hS2 hD1 hD2
    obtain ⟨x, rest', rfl⟩ := List.exists_cons_of_ne_nil hr
    have hns := hg.1
    rw [show A ++ p :: x :: rest' = (A ++ [p]) ++ x :: rest' by simp, NS_append] at hns
    obtain ⟨_, hx1, hx2, hx3⟩ := hns
    rw [show S0 ++ (A ++ [p]) = S0 ++ A ++ [p] by simp] at hx1 hx2 hx3
    unfold node
    simp only []
    split
    · rfl
    · rename_i h31
      have hx31 : x ≠ 31 := by rintro rfl; exact h31 (P2 31 hx2 hx1)
      have hr' : rest' ≠ [] := by
        rintro rfl
        have := hg.2.2
        simp at this
        exact hx31 this
      have hxlt : x < 1024 := hlt x (by simp)
      rw [List.any_eq_true]
      refine ⟨x, ?_, ?_⟩
      · by_cases hdx : dv (S0 ++ A) x
        · apply List.mem_append_left
          rw [List.mem_filter]
          refine ⟨hDl x hdx (fun h => hx1 (List.mem_append_left _ h)), ?_⟩
          have hpx : p < x := hc.1 A p x rest' rfl hr' hdx
          have hsb : Sb.testBit x = false := by
            cases h : Sb.testBit x
            · rfl
            · exact absurd ((hSb x).mp h) hx1
          simp [hpx, hsb]
        · apply List.mem_append_right
          rw [fresh_mem]
          refine ⟨P3 x hx2 hdx hx1, ?_⟩
          rw [Nat.testBit_lor]
          have e1 : Db.testBit x = false := by
            cases h : Db.testBit x
            · rfl
            · exact absurd (hD1 x h) hdx
          have e2 : Sb.testBit x = false := by
            cases h : Sb.testBit x
            · rfl
            · exact absurd ((hSb x).mp h) hx1
          rw [e1, e2]; rfl
      · have e : A ++ p :: x :: rest' = (A ++ [p]) ++ x :: rest' := by simp
        rw [e] at hg hc
        have eS : S0 ++ (A ++ [p]) = S0 ++ A ++ [p] := by simp
        apply ih (A ++ [p]) x rest' (Sop ++ [x]) _ _ _ _ hg hc hr' (by simp at hlen ⊢; omega)
        · intro y hy
          rw [eS]
          simp only [List.mem_append, List.mem_singleton] at hy ⊢
          rcases hy with hy | rfl
          · have := hS1 y hy; simp only [List.mem_append, List.mem_singleton] at this; tauto
          · right; rfl
        · intro y hy
          rw [eS] at hy
          simp only [List.mem_append, List.mem_singleton] at hy
          rcases hy with hy | rfl
          · rcases hS2 y (by rw [List.mem_append, List.mem_append, List.mem_singleton]; exact hy) with h | h | h
            · left; simp [h]
            · right; left; exact h
            · right; right; exact h
          · left; simp
        · intro v
          rw [tb_or_shift, eS]
          simp only [Bool.or_eq_true, decide_eq_true_eq, hSb v, List.mem_append, List.mem_singleton]
          constructor
          · rintro (h | rfl)
            · exact Or.inl h
            · exact Or.inr rfl
          · rintro (h | rfl)
            · exact Or.inl h
            · exact Or.inr rfl
        · intro v hv hvS
          rw [eS] at hv hvS
          by_cases hd : dv (S0 ++ A) v
          · exact List.mem_append_left _ (hDl v hd (fun h => hvS (List.mem_append_left _ h)))
          · apply List.mem_append_right
            rw [fresh_mem]
            refine ⟨P3 v hv hd hvS, ?_⟩
            cases h : Db.testBit v
            · rfl
            · exact absurd (hD1 v h) hd
        · intro v hv; rw [eS]; exact P1 v hv
        · intro v hv hvS; rw [eS] at hv hvS; exact P2 v hv hvS
        · intro y c hcm hc31 hy hyc
          rw [eS] at hcm
          rw [Nat.testBit_lor]
          simp only [List.mem_append, List.mem_singleton] at hcm
          rcases hcm with hcm | rfl
          · rw [hG y c (by rw [List.mem_append, List.mem_append, List.mem_singleton]; exact hcm) hc31 hy hyc]; rfl
          · rw [gtab_sound c y hxlt hc31 hy hyc]; simp

theorem dv_S0_iff (v : ℕ) : dv S0 v ↔ v ∈ D0 := by
  rw [D0, fresh_mem]
  simp only [Nat.zero_testBit, and_true, List.mem_flatMap, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false]
  constructor
  · rintro ⟨a, ha, b, hb, e⟩; exact ⟨a, ha, b, hb, e⟩
  · rintro ⟨a, ha, b, hb, e⟩; exact ⟨a, ha, b, hb, e⟩

theorem roots_okb : D0.all (fun v => S0.contains v || !(perms.all fun g => decide (v ≤ sigma g v)) ||
    roots.contains v) = true := by decide +kernel

theorem roots_ok (v : ℕ) (h1 : v ∈ D0) (h2 : v ∉ S0) (h3 : ∀ g ∈ perms, v ≤ sigma g v) : v ∈ roots := by
  have := List.all_eq_true.mp roots_okb v h1
  simp only [Bool.or_eq_true, List.contains_iff_mem, Bool.not_eq_true', List.all_eq_false,
    decide_eq_false_iff_not, not_le] at this
  rcases this with (h | ⟨g, hg, hlt⟩) | h
  · exact absurd h h2
  · exfalso; have h3' := h3 g hg; revert hlt; simp [h3']
  · exact h

theorem P0_sub : ∀ x ∈ P0, x ∈ S0 := by decide

theorem S0_in : ∀ x ∈ S0, x ∈ P0 ∨ x = 0 ∨ x = 1023 := by decide

theorem not31_D0 : (31 : ℕ) ∉ D0 := by decide +kernel

theorem foldl_or_tb (f : ℕ → ℕ) : ∀ (l : List ℕ) (acc x : ℕ),
    (l.foldl (fun g c => g ||| f c) acc).testBit x = true ↔ acc.testBit x = true ∨ ∃ c ∈ l, (f c).testBit x = true
  | [], acc, x => by simp
  | c :: l, acc, x => by
    rw [List.foldl_cons, foldl_or_tb f l, Nat.testBit_lor]
    simp only [Bool.or_eq_true, List.mem_cons]
    constructor
    · rintro ((h | h) | ⟨d, hd, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨c, Or.inl rfl, h⟩
      · exact Or.inr ⟨d, Or.inr hd, h⟩
    · rintro (h | ⟨d, rfl | hd, h⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨d, hd, h⟩

set_option maxHeartbeats 100000000 in
theorem run0 : rootRun 1 = false := by decide +kernel

set_option maxHeartbeats 100000000 in
theorem run1 : rootRun 32 = false := by decide +kernel

set_option maxHeartbeats 100000000 in
theorem run2 : rootRun 381 = false := by decide +kernel

set_option maxHeartbeats 100000000 in
theorem run3 : rootRun 494 = false := by decide +kernel

theorem roots_false (v : ℕ) (hv : v ∈ roots) : rootRun v = false := by
  simp only [roots, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  exacts [run0, run1, run2, run3]

theorem c5_bound (l : List ℕ) (h : VC S0 l 6) : (31 : ℕ) ∉ S0 ++ l := by
  intro hT
  obtain ⟨ns, h1, h2, h3⟩ := VC_to_NS l S0 6 h
  have hT' := h3 31 hT
  have hns : (31 : ℕ) ∈ ns := by
    rcases List.mem_append.mp hT' with h | h
    · exact absurd h (by decide)
    · exact h
  obtain ⟨ns1, a1, a2, a3⟩ := NS_trunc ns S0 31 h1 hns
  obtain ⟨ns2, hg, hc⟩ := canon_exists _ ns1 ⟨a1, by omega, a3⟩ rfl
  obtain ⟨v, rest, rfl⟩ : ∃ v rest, ns2 = v :: rest := by
    cases ns2 with
    | nil => have := hg.2.2; simp at this
    | cons v rest => exact ⟨v, rest, rfl⟩
  obtain ⟨hv1, hv2, _⟩ := hg.1
  have hvD : v ∈ D0 := (dv_S0_iff v).mp hv2
  have hv31 : v ≠ 31 := by rintro rfl; exact not31_D0 hvD
  have hrest : rest ≠ [] := by
    rintro rfl; have := hg.2.2; simp at this; exact hv31 this
  have hroot : v ∈ roots := roots_ok v hvD hv1 (hc.2 v rfl)
  have hvlt : v < 1024 := Gd_lt hg v (by simp)
  have key := node_sound 3 [] v rest (P0 ++ [v]) (addBits (S0 ++ [v]) 0) D0 (addBits D0 0)
    (G0 ||| gtab v) (by simpa using hg) (by simpa using hc) hrest (by simp)
    (by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ (List.mem_append_left _ (P0_sub x hx))
      · exact List.mem_append_right _ hx)
    (by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rw [List.append_nil] at hx
        rcases S0_in x hx with h | h | h
        · exact Or.inl (List.mem_append_left _ h)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · exact Or.inl (List.mem_append_right _ hx))
    (by
      intro w
      rw [addBits_tb]
      simp)
    (by
      intro w hw _
      exact (dv_S0_iff w).mp (by simpa using hw))
    (by
      intro w hw
      rw [addBits_tb] at hw
      simp only [Nat.zero_testBit, Bool.false_eq_true, false_or] at hw
      simpa using (dv_S0_iff w).mpr hw)
    (by
      intro w hw _
      rw [addBits_tb]
      right; exact (dv_S0_iff w).mp (by simpa using hw))
    (by
      intro x c hcm hc31 hx hxc
      rw [Nat.testBit_lor]
      simp only [List.nil_append, List.mem_append, List.mem_singleton] at hcm
      rcases hcm with hcm | rfl
      · have hcm : c ∈ S0 := by
          rcases hcm with h | h
          · exact h
          · simp at h
        have : G0.testBit x = true := by
          rw [G0, foldl_or_tb]
          right; exact ⟨c, hcm, gtab_sound c x (S0_lt c hcm) hc31 hx hxc⟩
        rw [this]; rfl
      · rw [gtab_sound c x hvlt hc31 hx hxc]; simp)
  have := roots_false v hroot
  rw [rootRun] at this
  rw [this] at key
  exact absurd key (by decide)

/-! ## Circuit evaluation -/

open PEqualNP.CircuitLowerBounds

def stepW (w : List Bool) (g : Gate) : List Bool := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Wl (gs : List Gate) (x : List Bool) : List Bool := gs.foldl stepW x

theorem Wl_length : ∀ (gs : List Gate) (x : List Bool), (Wl gs x).length = x.length + gs.length
  | [], x => by simp [Wl]
  | g :: gs, x => by
    have : Wl (g :: gs) x = Wl gs (stepW x g) := rfl
    rw [this, Wl_length gs, stepW]
    simp; omega

theorem Wl_prefix : ∀ (gs : List Gate) (x : List Bool), ∃ r, Wl gs x = x ++ r
  | [], x => ⟨[], by simp [Wl]⟩
  | g :: gs, x => by
    have : Wl (g :: gs) x = Wl gs (stepW x g) := rfl
    obtain ⟨r, hr⟩ := Wl_prefix gs (stepW x g)
    refine ⟨[g.op.eval (g.inputs.map fun i => x.getD i false)] ++ r, ?_⟩
    rw [this, hr, stepW, List.append_assoc]

theorem getD_app_left {l r : List Bool} {i : ℕ} (h : i < l.length) : (l ++ r).getD i false = l.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_ge {l : List Bool} {i : ℕ} (h : l.length ≤ i) : l.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

def val (C : Circuit) (x : List Bool) (w : ℕ) : Bool := (C.wires x).getD w false

theorem val_input (C : Circuit) (x : List Bool) (i : ℕ) (h : i < x.length) : val C x i = x.getD i false := by
  unfold val Circuit.wires
  obtain ⟨r, hr⟩ := Wl_prefix C.gates x
  have : C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x = Wl C.gates x := rfl
  rw [this, hr, getD_app_left h]

theorem val_big (C : Circuit) (x : List Bool) (i : ℕ) (h : x.length + C.gates.length ≤ i) : val C x i = false := by
  unfold val Circuit.wires
  have : C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x = Wl C.gates x := rfl
  rw [this]; exact getD_ge (by rw [Wl_length]; exact h)

theorem val_gate (C : Circuit) (x : List Bool) (t : ℕ) (ht : t < C.gates.length) :
    val C x (x.length + t) = (C.gates[t]).op.eval ((C.gates[t]).inputs.map fun i =>
      if i < x.length + t then val C x i else false) := by
  have hW : C.wires x = Wl C.gates x := rfl
  have hsplit : C.gates = C.gates.take t ++ (C.gates[t] :: C.gates.drop (t + 1)) := by
    rw [← List.drop_eq_getElem_cons ht, List.take_append_drop]
  have e1 : Wl C.gates x = Wl (C.gates.drop (t + 1)) (stepW (Wl (C.gates.take t) x) C.gates[t]) := by
    conv_lhs => rw [hsplit]
    rw [Wl, List.foldl_append, List.foldl_cons]; rfl
  have hlen : (Wl (C.gates.take t) x).length = x.length + t := by
    rw [Wl_length, List.length_take]; omega
  have pre : ∀ i, (Wl (C.gates.take t) x).getD i false = if i < x.length + t then val C x i else false := by
    intro i
    split
    · rename_i hi
      unfold val
      rw [hW, e1]
      obtain ⟨r, hr⟩ := Wl_prefix (C.gates.drop (t + 1)) (stepW (Wl (C.gates.take t) x) C.gates[t])
      rw [hr, stepW, List.append_assoc, getD_app_left (by rw [hlen]; exact hi)]
    · rename_i hi
      exact getD_ge (by rw [hlen]; omega)
  have key : (C.wires x).getD (x.length + t) false = (C.gates[t]).op.eval ((C.gates[t]).inputs.map
      fun i => (Wl (C.gates.take t) x).getD i false) := by
    rw [hW, e1]
    obtain ⟨r, hr⟩ := Wl_prefix (C.gates.drop (t + 1)) (stepW (Wl (C.gates.take t) x) C.gates[t])
    rw [hr, stepW, List.append_assoc]
    rw [show x.length + t = (Wl (C.gates.take t) x).length from hlen.symm]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
    simp only [List.cons_append, List.getElem?_cons_zero, Option.getD_some]
  rw [show val C x (x.length + t) = (C.wires x).getD (x.length + t) false from rfl, key]
  congr 1
  apply List.map_congr_left
  intro i _
  exact pre i

/-! ## Points, vectors, generic facts -/

def P (s : List ℕ) : Fin 6 → Bool := fun i => decide (i.val ∈ s)

def X (s : List ℕ) : List Bool := List.ofFn (P s)

theorem X_length (s : List ℕ) : (X s).length = 6 := by simp [X]

theorem X_getD (s : List ℕ) (i : ℕ) (hi : i < 6) : (X s).getD i false = decide (i ∈ s) := by
  rw [List.getD_eq_getElem?_getD, X, List.getElem?_ofFn]
  simp [hi, P]

def pat (p : ℕ) : List ℕ :=
  [[0, 1], [1, 2], [2, 3], [3, 4], [0, 4], [0, 2], [1, 3], [2, 4], [0, 3], [1, 4]].getD p []

def vecOf (f : ℕ → Bool) : ℕ := piV ((List.range 10).map f)

theorem vecOf_tb (f : ℕ → Bool) (i : ℕ) : (vecOf f).testBit i = (decide (i < 10) && f i) := by
  rw [vecOf, piV_tb]
  by_cases hi : i < 10
  · simp [hi, List.getD_eq_getElem?_getD]
  · simp [hi, List.getD_eq_getElem?_getD]

theorem vecOf_ext {f g : ℕ → Bool} (h : ∀ p < 10, f p = g p) : vecOf f = vecOf g := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [vecOf_tb, vecOf_tb]
  by_cases hi : i < 10
  · simp [hi, h i hi]
  · simp [hi]

theorem vecOf_and (f g : ℕ → Bool) : vecOf (fun p => f p && g p) = vecOf f &&& vecOf g := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_land, vecOf_tb, vecOf_tb, vecOf_tb]
  cases decide (i < 10) <;> simp

theorem vecOf_or (f g : ℕ → Bool) : vecOf (fun p => f p || g p) = vecOf f ||| vecOf g := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_lor, vecOf_tb, vecOf_tb, vecOf_tb]
  cases decide (i < 10) <;> simp

theorem vecOf_false : vecOf (fun _ => false) = 0 := by decide

theorem vecOf_true : vecOf (fun _ => true) = 1023 := by decide

theorem vecOf_zero {f : ℕ → Bool} (h : ∀ p < 10, f p = false) : vecOf f = 0 := by
  rw [vecOf_ext h, vecOf_false]

def gt (C : Circuit) (t : ℕ) : Gate := C.gates.getD t ⟨GateOp.or, []⟩

theorem gt_eq (C : Circuit) (t : ℕ) (ht : t < C.gates.length) : gt C t = C.gates[t] := by
  simp [gt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]

theorem val_gt (C : Circuit) (s : List ℕ) (t : ℕ) (ht : t < C.gates.length) :
    val C (X s) (6 + t) = (gt C t).op.eval ((gt C t).inputs.map fun i =>
      if i < 6 + t then val C (X s) i else false) := by
  have := val_gate C (X s) t ht
  rw [X_length] at this
  rw [this, gt_eq C t ht]

theorem val_in (C : Circuit) (s : List ℕ) (i : ℕ) (hi : i < 6) : val C (X s) i = decide (i ∈ s) := by
  rw [val_input C (X s) i (by rw [X_length]; exact hi), X_getD s i hi]

theorem val_out (C : Circuit) (s : List ℕ) (i : ℕ) (hi : 6 + C.gates.length ≤ i) : val C (X s) i = false :=
  val_big C (X s) i (by rw [X_length]; exact hi)

def reads (C : Circuit) (t w : ℕ) : Prop := w ∈ (gt C t).inputs ∧ w < 6 + t

def Mono (C : Circuit) : Prop := ∀ t < C.gates.length,
  ((gt C t).op = GateOp.and ∨ (gt C t).op = GateOp.or) ∧ (gt C t).inputs.length ≤ 2

theorem eval_congr (op : GateOp) (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i ∈ l, f i = g i) :
    op.eval (l.map f) = op.eval (l.map g) := by
  rw [List.map_congr_left h]

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ) (f g : ℕ → Bool)
    (h : ∀ i ∈ l, f i = true → g i = true) (hf : op.eval (l.map f) = true) : op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at hf ⊢
    rintro _ ⟨i, hi, rfl⟩
    exact h i hi (hf _ ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at hf ⊢
    obtain ⟨_, ⟨i, hi, rfl⟩, h2⟩ := hf
    exact ⟨_, ⟨i, hi, rfl⟩, h i hi h2⟩

/-- agreement of one circuit on two inputs, outside a set of wires -/
theorem agree (C : Circuit) (s s' : List ℕ) (E : ℕ → Prop)
    (ha : ∀ i < 6, ¬ E i → decide (i ∈ s) = decide (i ∈ s'))
    (hb : ∀ t < C.gates.length, ¬ E (6 + t) → ∀ i, reads C t i → E i → val C (X s) i = val C (X s') i) :
    ∀ w, ¬ E w → val C (X s) w = val C (X s') w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h6 : w < 6
    · rw [val_in C s w h6, val_in C s' w h6]; exact ha w h6 hw
    · by_cases hN : w < 6 + C.gates.length
      · obtain ⟨t, rfl⟩ : ∃ t, w = 6 + t := ⟨w - 6, by omega⟩
        rw [val_gt C s t (by omega), val_gt C s' t (by omega)]
        apply eval_congr
        intro i hi
        split
        · rename_i hit
          by_cases hE : E i
          · exact hb t (by omega) hw i ⟨hi, hit⟩ hE
          · exact ih i hit hE
        · rfl
      · rw [val_out C s w (by omega), val_out C s' w (by omega)]

/-- the circuit with the gates of c made constant false -/
def modC (C : Circuit) (c : List ℕ) : Circuit :=
  ⟨C.gates.mapIdx (fun t g => if t ∈ c then ⟨GateOp.or, []⟩ else g), C.output⟩

theorem modC_len (C : Circuit) (c : List ℕ) : (modC C c).gates.length = C.gates.length := by
  simp [modC]

theorem gt_modC (C : Circuit) (c : List ℕ) (t : ℕ) (ht : t < C.gates.length) :
    gt (modC C c) t = if t ∈ c then ⟨GateOp.or, []⟩ else gt C t := by
  rw [gt_eq _ t (by rw [modC_len]; exact ht), gt_eq C t ht]
  simp [modC, List.getElem_mapIdx]

theorem reads_modC (C : Circuit) (c : List ℕ) (t w : ℕ) (ht : t < C.gates.length) (htc : t ∉ c) :
    reads (modC C c) t w ↔ reads C t w := by
  simp [reads, gt_modC C c t ht, htc]

theorem Mono_modC (C : Circuit) (c : List ℕ) (h : Mono C) : Mono (modC C c) := by
  intro t ht
  rw [modC_len] at ht
  rw [gt_modC C c t ht]
  split
  · simp
  · exact h t ht

theorem faith (C : Circuit) (c : List ℕ) (s : List ℕ) (E : ℕ → Prop)
    (hE : ∀ t < C.gates.length, ¬ E (6 + t) → t ∉ c ∧ ∀ i, reads C t i → ¬ E i) :
    ∀ w, ¬ E w → val (modC C c) (X s) w = val C (X s) w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h6 : w < 6
    · rw [val_in _ s w h6, val_in C s w h6]
    · by_cases hN : w < 6 + C.gates.length
      · obtain ⟨t, rfl⟩ : ∃ t, w = 6 + t := ⟨w - 6, by omega⟩
        have ht : t < C.gates.length := by omega
        obtain ⟨htc, hr⟩ := hE t ht hw
        rw [val_gt _ s t (by rw [modC_len]; exact ht), val_gt C s t ht, gt_modC C c t ht, if_neg htc]
        apply eval_congr
        intro i hi
        split
        · rename_i hit
          exact ih i hit (hr i ⟨hi, hit⟩)
        · rfl
      · rw [val_out _ s w (by rw [modC_len]; omega), val_out C s w (by omega)]

theorem psi_le (C : Circuit) (hm : Mono C) (c : List ℕ) (s : List ℕ) (A : Bool)
    (hZ : ∀ t ∈ c, t < C.gates.length → val C (X s) (6 + t) = true → A = true) :
    ∀ w, (val (modC C c) (X s) w = true → val C (X s) w = true) ∧
      (A = false → val (modC C c) (X s) w = val C (X s) w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h6 : w < 6
    · rw [val_in _ s w h6, val_in C s w h6]; exact ⟨id, fun _ => rfl⟩
    · by_cases hN : w < 6 + C.gates.length
      · obtain ⟨t, rfl⟩ : ∃ t, w = 6 + t := ⟨w - 6, by omega⟩
        have ht : t < C.gates.length := by omega
        rw [val_gt _ s t (by rw [modC_len]; exact ht), val_gt C s t ht, gt_modC C c t ht]
        split
        · rename_i htc
          refine ⟨fun h => by simp [GateOp.eval] at h, fun hA => ?_⟩
          have : (gt C t).op.eval ((gt C t).inputs.map fun i => if i < 6 + t then val C (X s) i else false) = false := by
            cases hv : (gt C t).op.eval ((gt C t).inputs.map fun i => if i < 6 + t then val C (X s) i else false)
            · rfl
            · have := hZ t htc ht (by rw [val_gt C s t ht]; exact hv)
              rw [hA] at this; exact absurd this (by simp)
          rw [this]; simp [GateOp.eval]
        · rename_i htc
          refine ⟨fun h => eval_mono _ (hm t ht).1 _ _ _ ?_ h, fun hA => eval_congr _ _ _ _ ?_⟩
          · intro i _ hi
            by_cases hit : i < 6 + t
            · simp only [hit, if_true] at hi ⊢; exact (ih i hit).1 hi
            · simp only [hit, if_false] at hi ⊢; exact hi
          · intro i _
            split
            · rename_i hit; exact (ih i hit).2 hA
            · rfl
      · rw [val_out _ s w (by rw [modC_len]; omega), val_out C s w (by omega)]
        exact ⟨id, fun _ => rfl⟩

/-! ## VC lemmas -/

theorem VC_mono : ∀ (l S : List ℕ) (k k' : ℕ), VC S l k → k ≤ k' → VC S l k'
  | [], _, _, _, _, _ => trivial
  | v :: l, S, k, k', h, hk => by
    rcases h with ⟨h1, h2⟩ | ⟨h0, h1, h2⟩
    · exact Or.inl ⟨h1, VC_mono l _ k k' h2 hk⟩
    · exact Or.inr ⟨by omega, h1, VC_mono l _ (k - 1) (k' - 1) h2 (by omega)⟩

theorem VC_append : ∀ (l1 l2 S : List ℕ) (k1 k2 : ℕ), VC S l1 k1 → VC (S ++ l1) l2 k2 →
    VC S (l1 ++ l2) (k1 + k2)
  | [], l2, S, k1, k2, _, h2 => by simpa using VC_mono l2 _ k2 (k1 + k2) (by simpa using h2) (by omega)
  | v :: l1, l2, S, k1, k2, h1, h2 => by
    rcases h1 with ⟨a1, a2⟩ | ⟨a0, a1, a2⟩
    · refine Or.inl ⟨a1, ?_⟩
      exact VC_append l1 l2 (S ++ [v]) k1 k2 a2 (by simpa using h2)
    · refine Or.inr ⟨by omega, a1, ?_⟩
      have := VC_append l1 l2 (S ++ [v]) (k1 - 1) k2 a2 (by simpa using h2)
      rw [show k1 + k2 - 1 = k1 - 1 + k2 by omega]; exact this

theorem VC_snoc_mem (l S : List ℕ) (k v : ℕ) (h : VC S l k) (hv : v ∈ S ++ l) : VC S (l ++ [v]) k := by
  have := VC_append l [v] S k 0 h (Or.inl ⟨hv, trivial⟩)
  simpa using this

theorem VC_snoc_dv (l S : List ℕ) (k v : ℕ) (h : VC S l k) (hv : dv (S ++ l) v) : VC S (l ++ [v]) (k + 1) :=
  VC_append l [v] S k 1 h (Or.inr ⟨by omega, hv, trivial⟩)

/-! ## Chains of OR gates above the hub variable -/

def prevW (c : List ℕ) (j : ℕ) : ℕ := if j = 0 then 5 else 6 + c.getD (j - 1) 0

def topW (c : List ℕ) : ℕ := prevW c c.length

def VChain (C : Circuit) (c : List ℕ) : Prop :=
  ∀ j < c.length, c.getD j 0 < C.gates.length ∧
    (∀ t < C.gates.length, reads C t (prevW c j) ↔ t = c.getD j 0) ∧
    ((gt C (c.getD j 0)).op = GateOp.or ∨ ∀ i ∈ (gt C (c.getD j 0)).inputs, i = prevW c j)

section chain
variable {C : Circuit} {c : List ℕ}

theorem prevW_succ (c : List ℕ) (j : ℕ) : prevW c (j + 1) = 6 + c.getD j 0 := by simp [prevW]

theorem prevW_zero (c : List ℕ) : prevW c 0 = 5 := by simp [prevW]

theorem ch_reads (hc : VChain C c) {j : ℕ} (hj : j < c.length) : reads C (c.getD j 0) (prevW c j) :=
  ((hc j hj).2.1 _ (hc j hj).1).mpr rfl

theorem ch_lt (hc : VChain C c) {j : ℕ} (hj : j < c.length) : prevW c j < 6 + c.getD j 0 :=
  (ch_reads hc hj).2

theorem ch_strict (hc : VChain C c) : ∀ k j, j < k → k < c.length → c.getD j 0 < c.getD k 0 := by
  intro k
  induction k with
  | zero => intro j hj; omega
  | succ k ih =>
    intro j hj hk
    have h1 := ch_lt hc hk
    rw [prevW_succ] at h1
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
    · have := ih j h (by omega); omega
    · omega

theorem ch_ge (hc : VChain C c) : ∀ j < c.length, j ≤ c.getD j 0 := by
  intro j
  induction j with
  | zero => intro _; omega
  | succ j ih =>
    intro hj
    have := ch_strict hc (j + 1) j (by omega) hj
    have := ih (by omega)
    omega

theorem ch_len (hc : VChain C c) : c.length ≤ C.gates.length := by
  rcases Nat.eq_zero_or_pos c.length with h | h
  · omega
  · have h1 := ch_ge hc (c.length - 1) (by omega)
    have h2 := (hc (c.length - 1) (by omega)).1
    omega

theorem prevW_lt (hc : VChain C c) {j k : ℕ} (hjk : j < k) (hk : k ≤ c.length) : prevW c j < prevW c k := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [prevW_succ]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [prevW_zero]; omega
  · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [prevW_succ]
    have := ch_strict hc k j (by omega) (by omega)
    omega

theorem prevW_inj (hc : VChain C c) {j k : ℕ} (hj : j ≤ c.length) (hk : k ≤ c.length)
    (h : prevW c j = prevW c k) : j = k := by
  rcases Nat.lt_trichotomy j k with hjk | hjk | hjk
  · have := prevW_lt hc hjk hk; omega
  · exact hjk
  · have := prevW_lt hc hjk hj; omega

theorem mem_chain {t : ℕ} : t ∈ c ↔ ∃ j < c.length, c.getD j 0 = t := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]⟩

theorem ch_step (hc : VChain C c) (hm : Mono C) (s : List ℕ) {j : ℕ} (hj : j < c.length)
    (h : val C (X s) (prevW c j) = true) : val C (X s) (prevW c (j + 1)) = true := by
  have hr := ch_reads hc hj
  have hN := (hc j hj).1
  rw [prevW_succ, val_gt C s _ hN]
  rcases (hc j hj).2.2 with hor | hcp
  · rw [hor]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    exact ⟨_, ⟨prevW c j, hr.1, rfl⟩, by rw [if_pos hr.2]; exact h⟩
  · have hall : ∀ i ∈ (gt C (c.getD j 0)).inputs,
        (if i < 6 + c.getD j 0 then val C (X s) i else false) = true := by
      intro i hi; rw [hcp i hi, if_pos hr.2]; exact h
    rcases (hm _ hN).1 with hop | hop <;> rw [hop]
    · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
      rintro _ ⟨i, hi, rfl⟩; exact hall i hi
    · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
      exact ⟨_, ⟨prevW c j, hr.1, rfl⟩, hall _ hr.1⟩

theorem ch_up (hc : VChain C c) (hm : Mono C) (s : List ℕ) :
    ∀ k j, j ≤ k → k ≤ c.length → val C (X s) (prevW c j) = true → val C (X s) (prevW c k) = true := by
  intro k
  induction k with
  | zero => intro j hj _ h; rw [show j = 0 by omega] at h; exact h
  | succ k ih =>
    intro j hj hk h
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hj) with h' | h'
    · exact ch_step hc hm s (by omega) (ih j (by omega) (by omega) h)
    · rw [← h']; exact h

theorem ch_x5 (hc : VChain C c) (hm : Mono C) (s : List ℕ) (h5 : 5 ∈ s) :
    ∀ j ≤ c.length, val C (X s) (prevW c j) = true := by
  intro j hj
  apply ch_up hc hm s j 0 (by omega) hj
  rw [prevW_zero, val_in C s 5 (by omega)]
  simp [h5]

theorem getD_snoc (c : List ℕ) (t j : ℕ) : (c ++ [t]).getD j 0 = if j < c.length then c.getD j 0 else if j = c.length then t else 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  by_cases h : j < c.length
  · simp [h, List.getElem?_append_left h]
  · rw [List.getElem?_append_right (by omega)]
    by_cases h' : j = c.length
    · subst h'; simp
    · simp [h, h']
      rw [List.getElem?_eq_none (by simp; omega)]; rfl

theorem prevW_snoc (c : List ℕ) (t j : ℕ) (hj : j ≤ c.length) : prevW (c ++ [t]) j = prevW c j := by
  unfold prevW
  split
  · rfl
  · rw [getD_snoc, if_pos (by omega)]

theorem ch_extend (hc : VChain C c) {t : ℕ} (ht : t < C.gates.length)
    (hu : ∀ t' < C.gates.length, reads C t' (topW c) ↔ t' = t)
    (he : (gt C t).op = GateOp.or ∨ ∀ i ∈ (gt C t).inputs, i = topW c) : VChain C (c ++ [t]) := by
  intro j hj
  simp only [List.length_append, List.length_singleton] at hj
  rw [getD_snoc, prevW_snoc c t j (by omega)]
  by_cases h : j < c.length
  · rw [if_pos h]; exact hc j h
  · rw [if_neg h, if_pos (by omega)]
    have : j = c.length := by omega
    subst this
    exact ⟨ht, hu, he⟩

theorem chain_max (hm : Mono C) : ∃ c, VChain C c ∧ ∀ t, ¬ VChain C (c ++ [t]) := by
  have aux : ∀ n c, VChain C c → C.gates.length - c.length = n →
      ∃ c', VChain C c' ∧ ∀ t, ¬ VChain C (c' ++ [t]) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro c hc hn
      by_cases h : ∃ t, VChain C (c ++ [t])
      · obtain ⟨t, ht⟩ := h
        have := ch_len ht
        have hl : (c ++ [t]).length = c.length + 1 := by simp
        exact ih _ (by omega) (c ++ [t]) ht rfl
      · simp only [not_exists] at h
        exact ⟨c, hc, h⟩
  exact aux _ [] (fun j hj => by simp at hj) rfl

end chain

/-! ## Vectors of a circuit on the ten rim points -/

def vw (D : Circuit) (w : ℕ) : ℕ := vecOf (fun p => val D (X (pat p)) w)

theorem vin_tab : ∀ i < 6, vecOf (fun p => decide (i ∈ pat p)) = [305, 579, 166, 332, 664, 0].getD i 0 := by
  decide

theorem tab_S0 : ∀ i < 6, [305, 579, 166, 332, 664, 0].getD i 0 ∈ S0 := by decide

theorem vw_in (D : Circuit) (i : ℕ) (hi : i < 6) : vw D i ∈ S0 := by
  have : vw D i = vecOf (fun p => decide (i ∈ pat p)) := by
    unfold vw; apply vecOf_ext; intro p _; exact val_in D (pat p) i hi
  rw [this, vin_tab i hi]
  exact tab_S0 i hi

theorem vw_five (D : Circuit) : vw D 5 = 0 := by
  have : vw D 5 = vecOf (fun p => decide (5 ∈ pat p)) := by
    unfold vw; apply vecOf_ext; intro p _; exact val_in D (pat p) 5 (by omega)
  rw [this, vin_tab 5 (by omega)]; rfl

theorem zero_S0 : (0 : ℕ) ∈ S0 := by decide

theorem full_S0 : (1023 : ℕ) ∈ S0 := by decide

theorem eval_dv (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ) (hl : l.length ≤ 2)
    (F : ℕ → ℕ → Bool) (Cur : List ℕ) (h0 : 0 ∈ Cur) (h1 : 1023 ∈ Cur)
    (hin : ∀ i ∈ l, vecOf (F i) ∈ Cur) : dv Cur (vecOf (fun p => op.eval (l.map fun i => F i p))) := by
  match l, hl, hin with
  | [], _, _ =>
    rcases hop with rfl | rfl
    · refine ⟨1023, h1, 1023, h1, Or.inl ?_⟩
      simp only [GateOp.eval, List.map_nil, List.all_nil]; rw [vecOf_true]; rfl
    · refine ⟨0, h0, 0, h0, Or.inl ?_⟩
      simp only [GateOp.eval, List.map_nil, List.any_nil]; rw [vecOf_false]; rfl
  | [i], _, hin =>
    have hi := hin i (by simp)
    refine ⟨vecOf (F i), hi, vecOf (F i), hi, Or.inl ?_⟩
    rw [Nat.and_self]
    rcases hop with rfl | rfl <;> (apply vecOf_ext; intro p _; simp [GateOp.eval])
  | [i, j], _, hin =>
    have hi := hin i (by simp)
    have hj := hin j (by simp)
    refine ⟨vecOf (F i), hi, vecOf (F j), hj, ?_⟩
    rcases hop with rfl | rfl
    · left; rw [← vecOf_and]; apply vecOf_ext; intro p _; simp [GateOp.eval]
    · right; rw [← vecOf_or]; apply vecOf_ext; intro p _; simp [GateOp.eval]
  | _ :: _ :: _ :: _, hl, _ => simp at hl

theorem eval_triv (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ) (hl : l.length ≤ 2)
    (F : ℕ → ℕ → Bool) (Cur : List ℕ) (h0 : 0 ∈ Cur)
    (hin : ∀ i ∈ l, vecOf (F i) ∈ Cur) (z : ℕ) (hz : z ∈ l) (hz0 : ∀ p < 10, F z p = false) :
    vecOf (fun p => op.eval (l.map fun i => F i p)) ∈ Cur := by
  have hzv : vecOf (F z) = 0 := vecOf_zero hz0
  match l, hl, hin, hz with
  | [], _, _, hz => simp at hz
  | [i], _, hin, hz =>
    have : i = z := by simp at hz; exact hz.symm
    subst this
    have := hin i (by simp)
    convert this using 1
    rcases hop with rfl | rfl <;> (apply vecOf_ext; intro p _; simp [GateOp.eval])
  | [i, j], _, hin, hz =>
    rcases hop with rfl | rfl
    · convert h0 using 1
      apply vecOf_zero; intro p hp
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl <;> simp [hz0 p hp]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · convert hin j (by simp) using 1
        apply vecOf_ext; intro p hp; simp [GateOp.eval, hz0 p hp]
      · convert hin i (by simp) using 1
        apply vecOf_ext; intro p hp; simp [GateOp.eval, hz0 p hp]
  | _ :: _ :: _ :: _, hl, _, _ => simp at hl

theorem out_notE {C : Circuit} {c : List ℕ} (hc : VChain C c) (hm : Mono C)
    (h0 : val C (X (pat 0)) C.output = true) (hh : val C (X [5]) C.output = false) :
    ¬ ∃ j ≤ c.length, C.output = prevW c j := by
  rintro ⟨j, hj, he⟩
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · rw [he, prevW_zero, val_in C _ 5 (by omega)] at h0
    exact absurd h0 (by decide)
  · rw [he, ch_x5 hc hm [5] (by simp) j hj] at hh
    exact absurd hh (by decide)

theorem ch_inj {C : Circuit} {c : List ℕ} (hc : VChain C c) {j k : ℕ} (hj : j < c.length) (hk : k < c.length)
    (h : c.getD j 0 = c.getD k 0) : j = k := by
  rcases Nat.lt_trichotomy j k with h' | h' | h'
  · have := ch_strict hc k j h' hk; omega
  · exact h'
  · have := ch_strict hc j k h' hj; omega

theorem chain_E {C : Circuit} {c : List ℕ} (hc : VChain C c) {t : ℕ} (ht : t ∈ c) :
    ∃ k ≤ c.length, 6 + t = prevW c k := by
  obtain ⟨k, hk, rfl⟩ := mem_chain.mp ht
  exact ⟨k + 1, hk, (prevW_succ c k).symm⟩

theorem top_ge {C : Circuit} {c : List ℕ} (hc : VChain C c) {j : ℕ} (hj : j < c.length) :
    6 + c.getD j 0 ≤ topW c := by
  unfold topW
  rw [← prevW_succ]
  rcases Nat.lt_or_ge (j + 1) c.length with h | h
  · exact le_of_lt (prevW_lt hc h le_rfl)
  · rw [show j + 1 = c.length by omega]

theorem count_contra (C : Circuit) (hm : Mono C) (hN : C.gates.length ≤ 8) (c : List ℕ) (hc : VChain C c)
    (hT0 : ∀ p < 10, val C (X (pat p)) C.output = decide (p < 5))
    (hT1 : ∀ p < 10, val C (X (pat p ++ [5])) C.output = true)
    (hThub : val C (X [5]) C.output = false)
    (Kp : ℕ → Prop) [DecidablePred Kp]
    (hKr : ∀ t < C.gates.length, Kp t → t ∉ c → ∃ z, reads C t z ∧ ∀ p < 10, val (modC C c) (X (pat p)) z = false)
    (fb : ℕ) (hfb : fb = 0 → (c = [] ∨ ∀ p < 10, val (modC C c) (X (pat p)) C.output = false))
    (hbud : C.gates.length - ((Finset.range C.gates.length).filter Kp).card + (c.length - 1) + fb ≤ 6) :
    False := by
  set N := C.gates.length with hNdef
  set C' := modC C c with hC'
  have hlen' : C'.gates.length = N := modC_len C c
  have hm' : Mono C' := Mono_modC C c hm
  set gv : List ℕ := (List.range N).map (fun t => vw C' (6 + t)) with hgv
  have gv_len : gv.length = N := by simp [hgv]
  have memV : ∀ t ≤ N, ∀ i < 6 + t, vw C' i ∈ S0 ++ gv.take t := by
    intro t ht i hi
    by_cases h6 : i < 6
    · exact List.mem_append_left _ (vw_in C' i h6)
    · apply List.mem_append_right
      rw [List.mem_iff_getElem]
      refine ⟨i - 6, by simp [hgv]; omega, ?_⟩
      simp only [hgv, List.getElem_take, List.getElem_map, List.getElem_range]
      rw [show 6 + (i - 6) = i by omega]
  have memG : ∀ i, vw C' i ∈ S0 ++ gv := by
    intro i
    by_cases hi : i < 6 + N
    · have := memV N le_rfl i hi
      rwa [List.take_of_length_le (by omega)] at this
    · have : vw C' i = 0 := vecOf_zero (fun p _ => val_out C' _ i (by rw [hlen']; omega))
      rw [this]; exact List.mem_append_left _ zero_S0
  -- gate vectors
  have gate_eq : ∀ t < N, vw C' (6 + t) = vecOf (fun p => (gt C' t).op.eval ((gt C' t).inputs.map
      fun i => (fun i p => if i < 6 + t then val C' (X (pat p)) i else false) i p)) := by
    intro t ht
    unfold vw; apply vecOf_ext; intro p _
    exact val_gt C' (pat p) t (by rw [hlen']; exact ht)
  have Fin_cur : ∀ t < N, ∀ i, vecOf ((fun i p => if i < 6 + t then val C' (X (pat p)) i else false) i) ∈ S0 ++ gv.take t := by
    intro t ht i
    by_cases hi : i < 6 + t
    · have : vecOf ((fun i p => if i < 6 + t then val C' (X (pat p)) i else false) i) = vw C' i := by
        apply vecOf_ext; intro p _; simp [hi]
      rw [this]; exact memV t (le_of_lt ht) i hi
    · have : vecOf ((fun i p => if i < 6 + t then val C' (X (pat p)) i else false) i) = 0 := by
        apply vecOf_zero; intro p _; simp [hi]
      rw [this]; exact List.mem_append_left _ zero_S0
  have gate_dv : ∀ t < N, dv (S0 ++ gv.take t) (vw C' (6 + t)) := by
    intro t ht
    rw [gate_eq t ht]
    exact eval_dv _ (hm' t (by rw [hlen']; exact ht)).1 _ (hm' t (by rw [hlen']; exact ht)).2 _ _
      (List.mem_append_left _ zero_S0) (List.mem_append_left _ full_S0) (fun i _ => Fin_cur t ht i)
  have gate_triv : ∀ t < N, Kp t → vw C' (6 + t) ∈ S0 ++ gv.take t := by
    intro t ht hk
    by_cases htc : t ∈ c
    · have : vw C' (6 + t) = 0 := by
        rw [gate_eq t ht, hC', gt_modC C c t ht, if_pos htc]
        apply vecOf_zero; intro p _; simp [GateOp.eval]
      rw [this]; exact List.mem_append_left _ zero_S0
    · obtain ⟨z, hz, hz0⟩ := hKr t ht hk htc
      have hz' := (reads_modC C c t z ht htc).mpr hz
      rw [gate_eq t ht]
      exact eval_triv _ (hm' t (by rw [hlen']; exact ht)).1 _ (hm' t (by rw [hlen']; exact ht)).2 _ _
        (List.mem_append_left _ zero_S0) (fun i _ => Fin_cur t ht i) z hz'.1
        (fun p hp => by simp [hz'.2, hz0 p hp])
  have htake : ∀ t < N, gv.take (t + 1) = gv.take t ++ [vw C' (6 + t)] := by
    intro t ht
    rw [List.take_succ]
    simp [hgv, ht]
  have gate_part : ∀ t ≤ N, VC S0 (gv.take t) (t - ((Finset.range t).filter Kp).card) := by
    intro t
    induction t with
    | zero => intro _; simp [VC]
    | succ t ih =>
      intro ht
      have ih' := ih (by omega)
      have hcard : ((Finset.range t).filter Kp).card ≤ t := by
        have := Finset.card_filter_le (Finset.range t) Kp
        simpa using this
      rw [htake t (by omega), Finset.range_add_one, Finset.filter_insert]
      by_cases hk : Kp t
      · rw [if_pos hk, Finset.card_insert_of_notMem (by simp)]
        have := VC_snoc_mem _ _ _ _ ih' (gate_triv t (by omega) hk)
        rwa [show t + 1 - (((Finset.range t).filter Kp).card + 1) = t - ((Finset.range t).filter Kp).card by omega]
      · rw [if_neg hk]
        have := VC_snoc_dv _ _ _ _ ih' (gate_dv t (by omega))
        rwa [show t - ((Finset.range t).filter Kp).card + 1 = t + 1 - ((Finset.range t).filter Kp).card by omega] at this
  have hG := gate_part N le_rfl
  rw [List.take_of_length_le (by omega)] at hG
  -- the chain part
  set av : List ℕ := (List.range c.length).map (fun j => vw C (6 + c.getD j 0)) with hav
  have av_get : ∀ j < c.length, av[j]? = some (vw C (6 + c.getD j 0)) := by
    intro j hj; simp [hav, hj]
  have prev_cur : ∀ j < c.length, vw C (prevW c j) ∈ S0 ++ gv ++ av.take j := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · rw [prevW_zero, vw_five]; exact List.mem_append_left _ (List.mem_append_left _ zero_S0)
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      apply List.mem_append_right
      rw [prevW_succ]
      have h : (av.take (k + 1))[k]? = some (vw C (6 + c.getD k 0)) := by
        rw [List.getElem?_take_of_lt (by omega), av_get k (by omega)]
      exact List.mem_of_getElem? h
  have faithful : ∀ j < c.length, ∀ i ∈ (gt C (c.getD j 0)).inputs, i ≠ prevW c j → i < 6 + c.getD j 0 →
      ∀ p, val C' (X (pat p)) i = val C (X (pat p)) i := by
    intro j hj i hi hne hlt p
    let E : ℕ → Prop := fun w => (∃ k ≤ c.length, w = prevW c k) ∨ 6 + c.getD j 0 ≤ w
    apply faith C c (pat p) E
    · intro t ht hE
      have htc : t ∉ c := fun h => hE (Or.inl (chain_E hc h))
      refine ⟨htc, ?_⟩
      intro i' hr hE'
      rcases hE' with ⟨k, hk, rfl⟩ | hge
      · rcases Nat.lt_or_ge k c.length with hk' | hk'
        · have := ((hc k hk').2.1 t ht).mp hr
          exact htc (this ▸ (mem_chain.mpr ⟨k, hk', rfl⟩))
        · have h1 := top_ge hc hj
          have h2 : k = c.length := by omega
          subst h2
          have := hr.2
          exact hE (Or.inr (by unfold topW at h1; omega))
      · exact hE (Or.inr (by have := hr.2; omega))
    · rintro (⟨k, hk, rfl⟩ | hge)
      · rcases Nat.lt_or_ge k c.length with hk' | hk'
        · have := ((hc k hk').2.1 (c.getD j 0) (hc j hj).1).mp ⟨hi, hlt⟩
          have := ch_inj hc hj hk' this
          subst this; exact hne rfl
        · have h1 := top_ge hc hj
          have h2 : k = c.length := by omega
          subst h2; unfold topW at h1; omega
      · omega
  have Gcur : ∀ j < c.length, ∀ i ∈ (gt C (c.getD j 0)).inputs,
      vecOf ((fun i p => if i < 6 + c.getD j 0 then val C (X (pat p)) i else false) i) ∈ S0 ++ gv ++ av.take j := by
    intro j hj i hi
    by_cases hr : i < 6 + c.getD j 0
    · by_cases he : i = prevW c j
      · have : vecOf ((fun i p => if i < 6 + c.getD j 0 then val C (X (pat p)) i else false) i) = vw C (prevW c j) := by
          unfold vw; apply vecOf_ext; intro p _; dsimp only; rw [if_pos hr, he]
        rw [this]; exact prev_cur j hj
      · have : vecOf ((fun i p => if i < 6 + c.getD j 0 then val C (X (pat p)) i else false) i) = vw C' i := by
          unfold vw; apply vecOf_ext; intro p _; dsimp only; rw [if_pos hr]; exact (faithful j hj i hi he hr p).symm
        rw [this]; exact List.mem_append_left _ (memG i)
    · have : vecOf ((fun i p => if i < 6 + c.getD j 0 then val C (X (pat p)) i else false) i) = 0 := by
        apply vecOf_zero; intro p _; dsimp only; rw [if_neg hr]
      rw [this]; exact List.mem_append_left _ (List.mem_append_left _ zero_S0)
  have aeq : ∀ j < c.length, vw C (6 + c.getD j 0) = vecOf (fun p => (gt C (c.getD j 0)).op.eval
      ((gt C (c.getD j 0)).inputs.map fun i =>
        (fun i p => if i < 6 + c.getD j 0 then val C (X (pat p)) i else false) i p)) := by
    intro j hj
    unfold vw; apply vecOf_ext; intro p _
    exact val_gt C (pat p) _ (hc j hj).1
  have atake : ∀ j < c.length, av.take (j + 1) = av.take j ++ [vw C (6 + c.getD j 0)] := by
    intro j hj
    rw [List.take_succ, av_get j hj]; rfl
  have a_part : ∀ j ≤ c.length, VC (S0 ++ gv) (av.take j) (j - 1) := by
    intro j
    induction j with
    | zero => intro _; simp [VC]
    | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      rw [atake j (by omega)]
      have hN' := (hc j (by omega)).1
      rcases Nat.eq_zero_or_pos j with rfl | hpos
      · apply VC_snoc_mem _ _ _ (vw C (6 + c.getD 0 0)) ih'
        rw [aeq 0 (by omega)]
        have hr0 := ch_reads hc (j := 0) (by omega)
        rw [prevW_zero] at hr0
        exact eval_triv _ (hm _ hN').1 _ (hm _ hN').2 _ _
          (List.mem_append_left _ (List.mem_append_left _ zero_S0)) (fun i hi => Gcur 0 (by omega) i hi) 5 hr0.1
          (fun p _ => by simp only [hr0.2, if_true]; rw [val_in C _ 5 (by omega)]; decide +revert)
      · have := VC_snoc_dv _ _ _ (vw C (6 + c.getD j 0)) ih' (by
          rw [aeq j (by omega)]
          exact eval_dv _ (hm _ hN').1 _ (hm _ hN').2 _ _
            (List.mem_append_left _ (List.mem_append_left _ zero_S0))
            (List.mem_append_left _ (List.mem_append_left _ full_S0)) (fun i hi => Gcur j (by omega) i hi))
        rwa [show j - 1 + 1 = j + 1 - 1 by omega] at this
  have hA := a_part c.length le_rfl
  rw [List.take_of_length_le (by simp [hav])] at hA
  -- the final element
  have top_cur : vw C (topW c) ∈ S0 ++ gv ++ av := by
    rcases Nat.eq_zero_or_pos c.length with h0 | hpos
    · unfold topW; rw [h0, prevW_zero, vw_five]
      exact List.mem_append_left _ (List.mem_append_left _ zero_S0)
    · apply List.mem_append_right
      have e : prevW c c.length = 6 + c.getD (c.length - 1) 0 := by unfold prevW; rw [if_neg (by omega)]
      unfold topW; rw [e]
      exact List.mem_of_getElem? (av_get (c.length - 1) (by omega))
  have out_cur : vw C' C.output ∈ S0 ++ gv ++ av := List.mem_append_left _ (memG _)
  -- the value of the final element
  have hnotE := out_notE hc hm (by rw [hT0 0 (by omega)]; rfl) hThub
  have S1 : vw C (topW c) ||| vw C' C.output = 31 := by
    unfold vw
    rw [← vecOf_or]
    rw [show (31 : ℕ) = vecOf (fun p => decide (p < 5)) by decide]
    apply vecOf_ext; intro p hp
    have hZ : ∀ t ∈ c, t < N → val C (X (pat p)) (6 + t) = true → val C (X (pat p)) (topW c) = true := by
      intro t ht _ hv
      obtain ⟨k, hk, he⟩ := chain_E hc ht
      rw [he] at hv
      exact ch_up hc hm (pat p) c.length k hk le_rfl hv
    cases hA' : val C (X (pat p)) (topW c)
    · have := (psi_le C hm c (pat p) (val C (X (pat p)) (topW c)) hZ C.output).2 hA'
      rw [hC'] at *; simp [this, hT0 p hp]
    · have hJ : val C (X (pat p)) C.output = val C (X (pat p ++ [5])) C.output := by
        apply agree C (pat p) (pat p ++ [5]) (fun w => ∃ k ≤ c.length, w = prevW c k)
        · intro i hi hE
          have : i ≠ 5 := fun h => hE ⟨0, by omega, by rw [prevW_zero]; exact h⟩
          simp [this]
        · intro t ht hE i hr ⟨k, hk, hik⟩
          subst hik
          rcases Nat.lt_or_ge k c.length with hk' | hk'
          · have := ((hc k hk').2.1 t ht).mp hr
            exact absurd ⟨k + 1, hk', by rw [prevW_succ, this]⟩ hE
          · have hk2 : k = c.length := by omega
            subst hk2
            have h1 := ch_x5 hc hm (pat p ++ [5]) (by simp) c.length le_rfl
            unfold topW at hA'
            rw [hA', h1]
        · exact hnotE
      rw [hT1 p hp, hT0 p hp] at hJ
      simp [hJ]
  -- assemble
  have hF : VC (S0 ++ (gv ++ av)) [vw C (topW c) ||| vw C' C.output] fb := by
    have hcur : ∀ x, x ∈ S0 ++ gv ++ av → x ∈ S0 ++ (gv ++ av) := by intro x hx; simpa using hx
    rcases Nat.eq_zero_or_pos fb with h0 | hpos
    · refine Or.inl ⟨hcur _ ?_, trivial⟩
      rcases hfb h0 with hc0 | hz
      · subst hc0
        have : vw C (topW []) = 0 := by unfold topW; simp [prevW_zero, vw_five]
        rw [this, Nat.zero_or]; exact out_cur
      · have : vw C' C.output = 0 := vecOf_zero hz
        rw [this, Nat.or_zero]; exact top_cur
    · exact Or.inr ⟨hpos, ⟨_, hcur _ top_cur, _, hcur _ out_cur, Or.inr rfl⟩, trivial⟩
  have hAll := VC_append (gv ++ av) [vw C (topW c) ||| vw C' C.output] S0 _ fb
    (VC_append gv av S0 _ _ hG hA) hF
  have h6 := VC_mono _ _ _ 6 hAll (by omega)
  apply c5_bound _ h6
  rw [S1]; simp

theorem agree_contra (C : Circuit) (E : ℕ → Prop) (hE5 : E 5) (hEo : ¬ E C.output)
    (hcl : ∀ t < C.gates.length, ¬ E (6 + t) → ∀ i, reads C t i → ¬ E i)
    (h0 : val C (X (pat 5)) C.output = false) (h1 : val C (X (pat 5 ++ [5])) C.output = true) : False := by
  have := agree C (pat 5) (pat 5 ++ [5]) E
    (fun i _ hi => by
      have : i ≠ 5 := fun h => hi (h ▸ hE5)
      simp [this])
    (fun t ht hE i hr hi => absurd hi (hcl t ht hE i hr)) C.output hEo
  rw [h0, h1] at this
  exact absurd this (by decide)

theorem pat_no5 : ∀ p < 10, (5 ∈ pat p) = False := by decide

theorem top_zero (C : Circuit) (c : List ℕ) (hc : VChain C c) :
    ∀ p < 10, val (modC C c) (X (pat p)) (topW c) = false := by
  intro p hp
  rcases Nat.eq_zero_or_pos c.length with h0 | hpos
  · unfold topW; rw [h0, prevW_zero, val_in _ _ 5 (by omega)]
    simp [pat_no5 p hp]
  · have e : topW c = 6 + c.getD (c.length - 1) 0 := by unfold topW prevW; rw [if_neg (by omega)]
    have hN := (hc (c.length - 1) (by omega)).1
    have hm : c.getD (c.length - 1) 0 ∈ c := mem_chain.mpr ⟨_, by omega, rfl⟩
    rw [e, val_gt _ _ _ (by rw [modC_len]; exact hN), gt_modC C c _ hN, if_pos hm]
    simp [GateOp.eval]

theorem reader_not_chain {C : Circuit} {c : List ℕ} (hc : VChain C c) {t : ℕ}
    (hr : reads C t (topW c)) : t ∉ c := by
  intro ht
  obtain ⟨j, hj, rfl⟩ := mem_chain.mp ht
  have := top_ge hc hj
  have := hr.2
  omega

theorem and_zero (op : GateOp) (hop : op = GateOp.and) (l : List ℕ) (F : ℕ → Bool) (z : ℕ) (hz : z ∈ l)
    (hz0 : F z = false) : op.eval (l.map F) = false := by
  subst hop
  cases h : (GateOp.and).eval (l.map F)
  · rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at h
    have := h (F z) ⟨z, hz, rfl⟩
    rw [hz0] at this; exact absurd this (by decide)

theorem chain_card {C : Circuit} {c : List ℕ} (hc : VChain C c) (Kp : ℕ → Prop) [DecidablePred Kp]
    (hK : ∀ t ∈ c, Kp t) (extra : Finset ℕ) (hex : ∀ t ∈ extra, Kp t ∧ t ∉ c ∧ t < C.gates.length) :
    c.length + extra.card ≤ ((Finset.range C.gates.length).filter Kp).card := by
  let Sc := (Finset.range c.length).image (fun j => c.getD j 0)
  have hSc : Sc.card = c.length := by
    rw [Finset.card_image_of_injOn]
    · simp
    · intro j hj k hk h
      simp only [Finset.coe_range, Set.mem_Iio] at hj hk
      exact ch_inj hc hj hk h
  have hdisj : Disjoint Sc extra := by
    rw [Finset.disjoint_left]
    intro t ht hte
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
    exact (hex _ hte).2.1 (mem_chain.mpr ⟨j, by simpa using hj, rfl⟩)
  have hsub : Sc ∪ extra ⊆ (Finset.range C.gates.length).filter Kp := by
    intro t ht
    rw [Finset.mem_filter, Finset.mem_range]
    rcases Finset.mem_union.mp ht with ht | ht
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
      have hj' : j < c.length := by simpa using hj
      exact ⟨(hc j hj').1, hK _ (mem_chain.mpr ⟨j, hj', rfl⟩)⟩
    · exact ⟨(hex t ht).2.2, (hex t ht).1⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hSc] at this
  exact this

theorem filter_le (N : ℕ) (Kp : ℕ → Prop) [DecidablePred Kp] : ((Finset.range N).filter Kp).card ≤ N := by
  have := Finset.card_filter_le (Finset.range N) Kp
  simpa using this

theorem main (C : Circuit) (hm2 : PEqualNP.MetaComplexity.Monotone2 C) (hs : C.size ≤ 8)
    (he : ∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈
      ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 5), (2, 5), (3, 5), (4, 5)] : List (ℕ × ℕ)) ∧
        x u = true ∧ x v = true)) : False := by
  have hm : Mono C := by
    intro t ht
    rw [gt_eq C t ht]
    obtain ⟨h1, h2⟩ := hm2 _ (List.getElem_mem ht)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact ⟨h1, h2⟩
  have hN : C.gates.length ≤ 8 := hs
  have hspec : ∀ s, val C (X s) C.output = decide (∃ u v : Fin 6, (u.val, v.val) ∈
      ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 5), (2, 5), (3, 5), (4, 5)] : List (ℕ × ℕ)) ∧
        P s u = true ∧ P s v = true) := by
    intro s
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact he (P s)
  have k0 : ∀ p < 10, decide (∃ u v : Fin 6, (u.val, v.val) ∈
      ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 5), (2, 5), (3, 5), (4, 5)] : List (ℕ × ℕ)) ∧
        P (pat p) u = true ∧ P (pat p) v = true) = decide (p < 5) := by decide
  have k1 : ∀ p < 10, decide (∃ u v : Fin 6, (u.val, v.val) ∈
      ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 5), (2, 5), (3, 5), (4, 5)] : List (ℕ × ℕ)) ∧
        P (pat p ++ [5]) u = true ∧ P (pat p ++ [5]) v = true) = true := by decide
  have k2 : decide (∃ u v : Fin 6, (u.val, v.val) ∈
      ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 5), (2, 5), (3, 5), (4, 5)] : List (ℕ × ℕ)) ∧
        P [5] u = true ∧ P [5] v = true) = false := by decide
  have hT0 : ∀ p < 10, val C (X (pat p)) C.output = decide (p < 5) := fun p hp => by rw [hspec, k0 p hp]
  have hT1 : ∀ p < 10, val C (X (pat p ++ [5])) C.output = true := fun p hp => by rw [hspec, k1 p hp]
  have hThub : val C (X [5]) C.output = false := by rw [hspec, k2]
  have h05 : val C (X (pat 5)) C.output = false := by rw [hT0 5 (by omega)]; rfl
  have h15 : val C (X (pat 5 ++ [5])) C.output = true := hT1 5 (by omega)
  obtain ⟨c, hc, hmax⟩ := chain_max hm
  have hnotE := out_notE hc hm (by rw [hT0 0 (by omega)]; rfl) hThub
  let E0 : ℕ → Prop := fun w => ∃ k ≤ c.length, w = prevW c k
  have hE05 : E0 5 := ⟨0, by omega, by rw [prevW_zero]⟩
  have lower : ∀ t < C.gates.length, ¬ E0 (6 + t) → ∀ k < c.length, ¬ reads C t (prevW c k) := by
    intro t ht hE k hk hr
    have := ((hc k hk).2.1 t ht).mp hr
    exact hE ⟨k + 1, hk, by rw [prevW_succ, this]⟩
  by_cases h1 : ∃ t < C.gates.length, reads C t (topW c)
  swap
  · apply agree_contra C E0 hE05 hnotE _ h05 h15
    intro t ht hE i hr ⟨k, hk, hik⟩
    subst hik
    rcases Nat.lt_or_ge k c.length with hk' | hk'
    · exact lower t ht hE k hk' hr
    · exact h1 ⟨t, ht, by rw [show k = c.length by omega] at hr; exact hr⟩
  obtain ⟨r, hrN, hr⟩ := h1
  have hrc := reader_not_chain hc hr
  have hz0 := top_zero C c hc
  set fb1 : ℕ := if c = [] then 0 else 1 with hfb1
  have fbspec : fb1 = 0 → (c = [] ∨ ∀ p < 10, val (modC C c) (X (pat p)) C.output = false) := by
    intro h; left; by_contra hne; rw [hfb1, if_neg hne] at h; exact absurd h (by decide)
  have fbnum : c.length - 1 + fb1 ≤ c.length := by
    rw [hfb1]; split
    · omega
    · rename_i hne; have : c.length ≠ 0 := fun h => hne (List.length_eq_zero_iff.mp h); omega
  by_cases h2 : ∃ t < C.gates.length, t ≠ r ∧ reads C t (topW c)
  · obtain ⟨t2, ht2N, ht2r, ht2⟩ := h2
    have ht2c := reader_not_chain hc ht2
    let Kp : ℕ → Prop := fun t => t ∈ c ∨ t = r ∨ t = t2
    have hcard := chain_card hc Kp (fun t ht => Or.inl ht) {r, t2} (by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact ⟨Or.inr (Or.inl rfl), hrc, hrN⟩
      · exact ⟨Or.inr (Or.inr rfl), ht2c, ht2N⟩)
    rw [Finset.card_pair (Ne.symm ht2r)] at hcard
    have := filter_le C.gates.length Kp
    apply count_contra C hm hN c hc hT0 hT1 hThub Kp _ fb1 fbspec (by omega)
    intro t ht hk htc
    rcases hk with h | rfl | rfl
    · exact absurd h htc
    · exact ⟨_, hr, hz0⟩
    · exact ⟨_, ht2, hz0⟩
  have huniq : ∀ t < C.gates.length, reads C t (topW c) ↔ t = r := by
    intro t ht
    constructor
    · intro h; by_contra hne; exact h2 ⟨t, ht, hne, h⟩
    · rintro rfl; exact hr
  by_cases hext : (gt C r).op = GateOp.or ∨ ∀ i ∈ (gt C r).inputs, i = topW c
  · exact hmax r (ch_extend hc hrN huniq hext)
  have hand : (gt C r).op = GateOp.and := by
    rcases (hm r hrN).1 with h | h
    · exact h
    · exact absurd (Or.inl h) hext
  have rzero : ∀ p < 10, val (modC C c) (X (pat p)) (6 + r) = false := by
    intro p hp
    rw [val_gt _ _ _ (by rw [modC_len]; exact hrN), gt_modC C c r hrN, if_neg hrc]
    apply and_zero _ hand _ _ (topW c) hr.1
    rw [if_pos hr.2]; exact hz0 p hp
  by_cases hout : C.output = 6 + r
  · rcases Nat.eq_zero_or_pos c.length with hc0 | hpos
    · have hc0' : c = [] := List.length_eq_zero_iff.mp hc0
      have := hT0 0 (by omega)
      rw [hout, val_gt C _ r hrN] at this
      rw [and_zero _ hand _ _ (topW c) hr.1 (by
        rw [if_pos hr.2]; subst hc0'; unfold topW; rw [List.length_nil, prevW_zero, val_in C _ 5 (by omega)]; decide)] at this
      exact absurd this (by decide)
    · let Kp : ℕ → Prop := fun t => t ∈ c ∨ t = r
      have hcard := chain_card hc Kp (fun t ht => Or.inl ht) {r} (by
        intro t ht
        simp only [Finset.mem_singleton] at ht
        subst ht
        exact ⟨Or.inr rfl, hrc, hrN⟩)
      rw [Finset.card_singleton] at hcard
      have := filter_le C.gates.length Kp
      apply count_contra C hm hN c hc hT0 hT1 hThub Kp _ 0 (fun _ => Or.inr (by rw [hout]; exact rzero)) (by omega)
      intro t ht hk htc
      rcases hk with h | rfl
      · exact absurd h htc
      · exact ⟨_, hr, hz0⟩
  by_cases h3 : ∃ t < C.gates.length, reads C t (6 + r)
  · obtain ⟨r', hr'N, hr'⟩ := h3
    have hrr : r ≠ r' := by intro h; subst h; have := hr'.2; omega
    have hr'c : r' ∉ c := by
      intro h
      obtain ⟨j, hj, rfl⟩ := mem_chain.mp h
      have := top_ge hc hj
      have := hr.2
      have := hr'.2
      omega
    let Kp : ℕ → Prop := fun t => t ∈ c ∨ t = r ∨ t = r'
    have hcard := chain_card hc Kp (fun t ht => Or.inl ht) {r, r'} (by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact ⟨Or.inr (Or.inl rfl), hrc, hrN⟩
      · exact ⟨Or.inr (Or.inr rfl), hr'c, hr'N⟩)
    rw [Finset.card_pair hrr] at hcard
    have := filter_le C.gates.length Kp
    apply count_contra C hm hN c hc hT0 hT1 hThub Kp _ fb1 fbspec (by omega)
    intro t ht hk htc
    rcases hk with h | rfl | rfl
    · exact absurd h htc
    · exact ⟨_, hr, hz0⟩
    · exact ⟨_, hr', rzero⟩
  · apply agree_contra C (fun w => E0 w ∨ w = 6 + r) (Or.inl hE05) _ _ h05 h15
    · rintro (h | h)
      · exact hnotE h
      · exact hout h
    · intro t ht hE i hri hi
      rcases hi with ⟨k, hk, rfl⟩ | rfl
      · rcases Nat.lt_or_ge k c.length with hk' | hk'
        · exact lower t ht (fun h => hE (Or.inl h)) k hk' hri
        · have : t = r := (huniq t ht).mp (by rw [show k = c.length by omega] at hri; exact hri)
          exact hE (Or.inr (by rw [this]))
      · exact h3 ⟨t, ht, hri⟩

end PEqualNP.Outside.L_meta_619

theorem PEqualNP.Outside.L_meta_619 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 5), (2, 5), (3, 5), (4, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  rintro ⟨C, hm, hs, he⟩
  exact PEqualNP.Outside.L_meta_619.main C hm hs he
