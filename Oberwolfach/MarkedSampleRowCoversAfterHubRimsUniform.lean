module

public import Oberwolfach.MarkedDeepBufferedEndpointProfilesUniform
public import Oberwolfach.MarkedDeepRowNumericBudget
public import Oberwolfach.MarkedEmptyPhysicalDeletion
public import Oberwolfach.MarkedSampleRootNeighbours
public import Oberwolfach.MarkedEndpointArcExhaustion
public import Oberwolfach.MarkedRowCoversAfterInitialRimDeletion
public import Oberwolfach.MarkedSampledHostCounts

@[expose] public section

/-! Successive deep-row covers in the actual current sampled host. The
endpoint degrees, cuts, class sizes, matching margins and path-extension
counts are derived from the original fixed profiles and parent degrees.
Only local balance at the rows being covered is required. The earlier
hub rim graph is deleted on the free set; its actual degree loss is
included in every path budget, and all new row rims avoid it. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 30000000
set_option maxRecDepth 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_sample_row_covers_after_hub_rims_uniform
    (l:ℕ) (hl:2≤l) (omega₀ t₀ rho₀ gamma eta:ℝ)
    (ho₀:0<omega₀) (ht₀:0<t₀) (ht₀1:t₀≤1) (hrho₀:0<rho₀) (hrho₀1:rho₀≤1)
    (hg:0<gamma) (hg1:gamma≤1) (heta:0<eta) (hetaSmall:eta≤t₀*(t₀*omega₀/2)/32):
    ∃ eps:ℝ,0<eps ∧ ∃ K:ℕ,0<K ∧ ∃ zeta:ℝ,0<zeta ∧
    ∀ d:ℕ,1≤d→∃ N:ℕ,1≤N ∧
    ∀ omega t rho:ℝ,omega₀≤omega → t₀≤t → rho₀≤rho → rho≤1 → ((l+3:ℕ):ℝ)*t≤1 →
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    N≤Fintype.card V→(Fintype.card U:ℝ)≤Fintype.card V→ omega*Fintype.card V≤(Fintype.card U:ℝ)→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V),
    (∀ x,(1/2+gamma/2)*Fintype.card V≤(P.degree x:ℝ))→
    (∀ x,|(P.degree x:ℝ)-2*Fintype.card U/rho|≤eps*Fintype.card V)→
    ∀ (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color),
    (∀ u,q u g=t)→(∀ u,s u j=((l+3:ℕ):ℝ)*t)→
    ∀ (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop),
    MarkedRowsWithSpokes P π d (l+11) Finset.univ (rho*(((l+3:ℕ):ℝ)*t)/2) (rho*t/2)
      q s g j (eps*Fintype.card V) σ H→
    MarkedIndicesWithSpokes π d (l+11) Finset.univ q s g j (eps*Fintype.card V) σ H→
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E₀=>e.val.1
    let head:=fun e:E₀=>e.val.2
    let ktail:=fun e:E₁=>e.val.1
    let khead:=fun e:E₁=>e.val.2
    ∀ (F:Finset V),(∀ x,π x∈F↔x∈F)→((Fᶜ).card:ℝ)≤zeta*Fintype.card V→
    ∀ hHub:ℕ,(hHub:ℝ)≤zeta*Fintype.card V→
    ∀ D:SimpleGraph V,GraphSupportedOn F D→(∀ x,(D.degree x:ℝ)≤(2*hHub:ℕ))→
    ∀ (m:ℕ) (v:Fin m→V),Function.Injective v→(m:ℝ)≤zeta*Fintype.card V→(∀ i,v i∉F)→
    (∀ i u,¬(H false (v i) u∧H true (v i) u))→
    (∀ i,∀ a:E₀⊕E₁,Sum.elim head khead a=v i→Sum.elim tail ktail a∈F)→
    (∀ i,∀ a:E₀⊕E₁,Sum.elim tail ktail a=v i→Sum.elim head khead a∈F)→
    (∀ i,(Finset.univ.filter (fun a:E₀⊕E₁=>Sum.elim head khead a=v i)).card=
      (Finset.univ.filter (fun a:E₀⊕E₁=>Sum.elim tail ktail a=v i)).card)→
    (∀ i,(Finset.univ.filter (fun a:E₀⊕E₁=>Sum.elim head khead a=v i)).card=
      (Finset.univ.filter (fun z:V×U=>(H false z.1 z.2∨H true z.1 z.2)∧z.1=v i)).card)→
    (∀ i,(Finset.univ.filter (fun a:E₀⊕E₁=>Sum.elim head khead a=v i∧markedArcType a=true)).card=
      (Finset.univ.filter (fun z:V×U=>H true z.1 z.2∧z.1=v i)).card)→
    let Y₀:=fun i=>Finset.univ.filter (H false (v i))
    let Y₁:=fun i=>Finset.univ.filter (H true (v i))
    let ain:=fun i=>markedEndpointTaggedArcEmbedding P π d Finset.univ true (v i) σ
    let xout:=fun i=>markedEndpointTaggedArcEmbedding P π d Finset.univ false (v i) σ
    ∃ C:Fin m→Finset (MarkedWheel tail head ktail khead (l+3) π (3*d) (H false) (H true)),
      (∀ i,MarkedRowCover (C i) (v i) F
        (markedRowRequiredResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
          (π:=π) (ain i) (xout i) (v i) (Y₀ i∪Y₁ i)) (Y₀ i∪Y₁ i) K) ∧
      (∀ i j,i≠j→Disjoint ((C i).biUnion markedWheelPhysicalResources)
        ((C j).biUnion markedWheelPhysicalResources)) ∧
      (∀ i,Disjoint (markedPackingRimGraph (C i)) D):=by
  let pstar:=rho₀*t₀/2
  have hpstar:0<pstar:=by dsimp [pstar];positivity
  have hpstar1:pstar≤1:=by dsimp [pstar];nlinarith [mul_nonneg (sub_nonneg.mpr hrho₀1) ht₀.le]
  let beta:=pstar^4*gamma/4
  let eext:=min beta (pstar^(l+11)/2)
  have hb:0<beta:=by dsimp [beta];positivity
  have hext:0<eext:=lt_min hb (by positivity)
  have hst':((l+4:ℕ):ℝ)-1=(l+3:ℕ):=by push_cast;ring
  obtain ⟨eps₀,heps₀,hprofiles⟩:=marked_deep_buffered_endpoint_profiles_uniform omega₀ t₀ eta ho₀ ht₀ ht₀1
    (l+4) (by omega) heta hetaSmall
  obtain ⟨K,hK,zeta₀,hzeta₀,hbudget⟩:=marked_deep_row_numeric_budget l beta 1 (t₀/4) eta hb
    (by norm_num) (by positivity) heta
  let eps:=min eps₀ (min eext (eext*omega₀))
  have heps:0<eps:=lt_min heps₀ (lt_min hext (mul_pos hext ho₀))
  have hep0:eps≤eps₀:=min_le_left _ _
  have hepe:eps≤eext:=(min_le_right _ _).trans (min_le_left _ _)
  have hepu:eps≤eext*omega₀:=(min_le_right _ _).trans (min_le_right _ _)
  let cap:ℝ:=K+l+8
  have hcap:0<cap:=by dsimp [cap];positivity
  let zeta:=min zeta₀ ((t₀*(t₀*omega₀/2)/4)/cap)
  have hzeta:0<zeta:=lt_min hzeta₀ (by positivity)
  have hz0:zeta≤zeta₀:=min_le_left _ _
  have hzcap:zeta*cap≤t₀*(t₀*omega₀/2)/4:=
    (le_div_iff₀ hcap).mp (min_le_right _ _)
  refine ⟨eps,heps,K,hK,zeta,hzeta,?_⟩
  intro d hd
  obtain ⟨N₀,hN₀,hprof⟩:=hprofiles d
  obtain ⟨N₁,hN₁,hbud⟩:=hbudget (3*d)
  obtain ⟨N₂,hN₂⟩:=exists_nat_gt (4*(6*(d:ℝ)+1)/gamma)
  refine ⟨max N₀ (max N₁ N₂),hN₀.trans (le_max_left _ _),?_⟩
  intro omega t rho hω htlo hρ hrho1 hst
  have ho:0<omega:=ho₀.trans_le hω
  have ht:0<t:=ht₀.trans_le htlo
  have hrho:0<rho:=hrho₀.trans_le hρ
  have hps0:pstar≤rho*t/2:=by
    dsimp [pstar]
    have hh:=mul_le_mul hρ htlo ht₀.le hrho.le
    linarith
  have hps:pstar≤t:=by nlinarith only [hps0,hrho1,ht]
  intro V U Γ Color _ _ _ _ _ _ hn hUn hU P π hdeg hparent q s g j hq hs σ H hr hi
  try dsimp only
  intro F hF hFc hHub hhub D hDF hD m v hv hm hvF hdis hinc hout hdir hrow hmark
  let n:=Fintype.card V
  have hn0:(0:ℝ)≤n:=Nat.cast_nonneg n
  have hnpos:0<n:=lt_of_lt_of_le Nat.zero_lt_one (hN₀.trans ((le_max_left _ _).trans hn))
  have hep0n:eps*n≤eps₀*n:=mul_le_mul_of_nonneg_right hep0 hn0
  have hpext:eps*n≤eext*n:=mul_le_mul_of_nonneg_right hepe hn0
  have hpextU:eps*n≤eext*Fintype.card U:=by
    have h1:=mul_le_mul_of_nonneg_right hepu hn0
    have hU₀:omega₀*(Fintype.card V:ℝ)≤Fintype.card U:=
      (mul_le_mul_of_nonneg_right hω hn0).trans hU
    have h2:=mul_le_mul_of_nonneg_left hU₀ hext.le
    dsimp only [n] at h1 ⊢
    nlinarith only [h1,h2]
  have hrows:MarkedRowsWithSpokes P π d (l+11) Finset.univ (rho*(((l+3:ℕ):ℝ)*t)/2) (rho*t/2)
      q s g j (eext*n) σ H:=by
    intro S T J hS hT hJ hinj
    exact (hr S T J hS hT hJ hinj).trans_le hpext
  have hindices:MarkedIndicesWithSpokes π d (l+11) Finset.univ q s g j (eext*Fintype.card U) σ H:=by
    intro J hJ hsep
    exact (hi J hJ hsep).trans_le hpextU
  have hloss:2*(2*(3*d:ℕ)+1:ℝ)≤gamma*n/2:=by
    have hnd:N₂≤n:=(le_max_right _ _).trans ((le_max_right _ _).trans hn)
    have hh:4*(6*(d:ℝ)+1)<(n:ℝ)*gamma:=
      (div_lt_iff₀ hg).mp (hN₂.trans_le (Nat.cast_le.mpr hnd))
    push_cast
    linarith only [hh]
  have hprob:pstar≤rho*(((l+3:ℕ):ℝ)*t)/2:=by
    have hl':(1:ℝ)≤(l+3:ℕ):=by exact_mod_cast (show 1≤l+3 by omega)
    have hh:=mul_le_mul_of_nonneg_left hl' (mul_pos hrho ht).le
    nlinarith only [hh,hps0]
  have hstlow:t≤((l+3:ℕ):ℝ)*t:=by
    have hl':(1:ℝ)≤(l+3:ℕ):=by exact_mod_cast (show 1≤l+3 by omega)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hl' ht.le
  have Q:=marked_sampled_host_extension_counts P π d l (rho*(((l+3:ℕ):ℝ)*t)/2) (rho*t/2)
    q s g j eext gamma pstar omega₀ hpstar hpstar1 hg hg1 hprob hps0
    (by intro u;rw [hq];exact hps) (by intro u;rw [hs];exact hps.trans hstlow)
    (min_le_left _ _) (min_le_right _ _) hloss hdeg ((mul_le_mul_of_nonneg_right hω hn0).trans hU) σ H hrows hindices
  have hprof':=hprof n ((le_max_left _ _).trans hn) omega t rho hω htlo hrho hrho1 (by simpa only [hst'] using hst) V U Γ Color rfl P π (l+11) (by omega)
    Finset.univ Finset.univ (by intro x;simp) (by simpa only [Finset.card_univ] using hU)
    (by simpa only [Finset.card_univ] using hUn) q s g j (fun u _=>hq u) (by intro u _;rw [hs,hst'])
    (eps*n) (eps*n) 0 0 0 (eps*n) (by positivity) (by positivity) (by norm_num) (by norm_num)
    (by norm_num) (by positivity) (by simpa using hep0n) (by simpa using hep0n) hep0n
    (by intro x;simpa only [Finset.inter_univ,Finset.card_univ,SimpleGraph.card_neighborFinset_eq_degree] using hparent x)
    σ H (by simpa only [hst'] using hr) hi ⊥ ⊥ (by simp) (by simp) (by simp)
  dsimp only at hprof'
  simp only [markedDeletePhysicalSpokes_bottom] at hprof'
  obtain ⟨_,_,hgap,hblocks,hdegree,hmargin⟩:=hprof'
  let L:=fun mark incoming x=>markedEndpointLabels P π d Finset.univ (mark,incoming,x) σ
  let Y:=fun mark x=>Finset.univ.filter (H mark x)
  have hgapReal (x:V):((L true false x).card:ℝ)+2*(eta*n)≤(Y false x).card:=by
    convert hgap x using 1
    congr 2
    congr 1
    ext z
    simp [L,markedEndpointLabels,rawMarkedPairRims,rawMarkedDeleteRims,markedPhysicalRim,
      permutationSeparatedMatrix,markedPhysicalOrientation]
  have hblocksReal (mark incoming:Bool) (x:V) (r typ:Bool) (loss:ℝ)
      (hLoss:loss≤(t₀*(t₀*omega₀/2)/4)*n):
      BipartiteBlockBounds (H typ) (fun z=>z∈L mark incoming x) (fun u=>u∈Y r x)
        ((t₀*(t₀*omega₀/2)/4)*n+loss) (eta*n) (2*(t₀/4)):=by
    convert hblocks (mark,incoming,x) r typ loss hLoss using 1
    funext z
    apply propext
    simp [L,markedEndpointLabels,rawMarkedPairRims,rawMarkedDeleteRims,markedPhysicalRim,
      permutationSeparatedMatrix,markedPhysicalOrientation]
  have hY (i:Fin m):Disjoint (Y false (v i)) (Y true (v i)):=marked_actual_spoke_rows_disjoint (H false) (H true) (v i) (hdis i)
  have hbals (i:Fin m):=(marked_sample_row_cardinal_balances P π d σ H (v i) (hdis i) (hdir i) (hrow i) (hmark i))
  have hYn (i:Fin m):(Y false (v i)).card+(Y true (v i)).card≤n:=by
    rw [←Finset.card_union_of_disjoint (hY i)]
    exact (Finset.card_le_univ _).trans (by exact_mod_cast hUn)
  have hm0:(m:ℝ)≤zeta₀*n:=hm.trans (mul_le_mul_of_nonneg_right hz0 hn0)
  have hhub0:(hHub:ℝ)≤zeta₀*n:=hhub.trans (mul_le_mul_of_nonneg_right hz0 hn0)
  have he0:((Fᶜ).card:ℝ)≤zeta₀*n:=hFc.trans (mul_le_mul_of_nonneg_right hz0 hn0)
  have hbud' (i:Fin m):=hbud n ((le_max_left _ _).trans ((le_max_right _ _).trans hn))
    hHub m (Fᶜ).card ((Y false (v i)).card+(Y true (v i)).card) hhub0 hm0 he0 (hYn i)
  have hlossCap:(m*(K+l+8):ℕ)≤(t₀*(t₀*omega₀/2)/4)*(n:ℝ):=by
    have h1:=mul_le_mul_of_nonneg_right hm hcap.le
    have h2:=mul_le_mul_of_nonneg_right hzcap hn0
    dsimp only [cap] at h1 h2
    push_cast
    nlinarith only [h1,h2]
  have hcutLoss:(m*(K+l+8):ℕ)≤(t₀/4)*(eta*(n:ℝ)):=by
    obtain ⟨_,_,_,hc,_⟩:=hbud n ((le_max_left _ _).trans ((le_max_right _ _).trans hn))
      0 m (Fᶜ).card 0 (by simpa only [Nat.cast_zero] using mul_nonneg hzeta₀.le hn0) hm0 he0 (Nat.zero_le _)
    exact hc
  have hsupport (incoming:Bool) (i:Fin m):L false incoming (v i)∪L true incoming (v i)⊆F:=by
    intro z hz
    rcases Finset.mem_union.mp hz with hz|hz
    · dsimp only [L] at hz
      rw [marked_endpoint_labels_actual] at hz
      have he:=(Finset.mem_filter.mp hz).2
      cases incoming
      · exact hout i (Sum.inl ⟨(v i,z),he⟩) rfl
      · exact hinc i (Sum.inl ⟨(z,v i),he⟩) rfl
    · dsimp only [L] at hz
      rw [marked_endpoint_labels_actual] at hz
      have he:=(Finset.mem_filter.mp hz).2
      cases incoming
      · exact hout i (Sum.inr ⟨(v i,z),he⟩) rfl
      · exact hinc i (Sum.inr ⟨(z,v i),he⟩) rfl
  have hsep (incoming:Bool) (i:Fin m):∀ z∈L false incoming (v i)∪L true incoming (v i),
      ¬PermutationClose π (3*d) z (v i):=by
    intro z hz hc
    rcases Finset.mem_union.mp hz with hz|hz
    all_goals
      exact marked_endpoint_labels_separated P π d Finset.univ _ σ z hz
        ((permutationClose_symm π (3*d) _ _).mp hc)
  apply marked_row_covers_after_initial_rim_deletion Q hl (by omega)
    (markedSampleArc_physical_injective P π (3*d) _) F hF D hDF (2*hHub:ℕ) (by positivity) hD v hv hvF
    (fun i=>L false true (v i)) (fun i=>L true true (v i))
    (fun i=>L false false (v i)) (fun i=>L true false (v i))
    (fun i=>Y false (v i)) (fun i=>Y true (v i)) hY
    (fun i=>markedEndpointTaggedArcEmbedding P π d Finset.univ true (v i) σ)
    (fun i=>markedEndpointTaggedArcEmbedding P π d Finset.univ false (v i) σ)
    (fun i a=>marked_endpoint_arc_embedding_head P π d Finset.univ true (v i) σ a)
    (fun i a=>marked_endpoint_arc_embedding_tail P π d Finset.univ true (v i) σ a)
    (fun i a=>marked_endpoint_arc_embedding_tail P π d Finset.univ false (v i) σ a)
    (fun i a=>marked_endpoint_arc_embedding_head P π d Finset.univ false (v i) σ a)
    (fun i a=>marked_endpoint_arc_embedding_type P π d Finset.univ true (v i) σ a)
    (fun i a=>marked_endpoint_arc_embedding_type P π d Finset.univ false (v i) σ a)
    (hsupport true) (hsupport false) (hsep true) (hsep false)
    (by intro i u hu;exact (Finset.mem_filter.mp hu).2) (by intro i u hu;exact (Finset.mem_filter.mp hu).2)
    (fun i=>(hbals i).1) (fun i=>(hbals i).2.1) (fun i=>(hbals i).2.2)
    K hK ((t₀*(t₀*omega₀/2)/4)*n) (eta*n) (t₀/4) (mul_pos heta (Nat.cast_pos.mpr hnpos)) (by positivity)
    hdegree hmargin (fun i=>hgapReal (v i)) (m*(K+l+8):ℕ)
    (by exact_mod_cast Nat.mul_le_mul_left m (show K+4≤K+l+8 by omega))
    (by exact_mod_cast Nat.mul_le_mul_left m (show l+4≤K+l+8 by omega)) hcutLoss
    (fun i=>hblocksReal true true (v i) true false _ hlossCap)
    (fun i=>hblocksReal false true (v i) false false _ hlossCap)
    (fun i=>hblocksReal true false (v i) false true _ hlossCap)
    (fun i=>hblocksReal false false (v i) false false _ hlossCap)
    (fun i=>hblocksReal false false (v i) true false _ hlossCap)
  intro i
  have hb:=(hbud' i).2.2.2.2
  convert hb using 1 <;> push_cast <;> ring

end Oberwolfach
