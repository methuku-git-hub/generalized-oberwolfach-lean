module

public import Oberwolfach.MarkedSampleCorrectionStarPacking
public import Oberwolfach.MarkedReservedSampleDeepCoverUniform

@[expose] public section

/-! Both deep-stage packings are constructed with every sufficiently small
prescribed-packing tolerance. Its choice follows the fixed domain-size
allowance and precedes the separation radius. The packings are constructed from the fixed sampled
profiles and the actual sparse inner correction. The constants are chosen
before the separation radius. Local balances, support and physical deletion
budgets are derived, rather than supplied as additional host assumptions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 50000000
set_option maxRecDepth 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_corrected_sample_deep_cover_controlled_uniform
    (r:ℕ) (hr:2≤r) (omega₀ t₀ rho₀ gamma eta:ℝ)
    (ho₀:0<omega₀) (ht₀:0<t₀) (ht₀1:t₀≤1) (hrho₀:0<rho₀) (hrho₀1:rho₀≤1)
    (hg:0<gamma) (hg1:gamma≤1) (heta:0<eta) (hetaSmall:eta≤t₀*(t₀*omega₀/2)/32)
    (β aLo B pstar:ℝ) (hβ:0<β) (hβt₀:β≤t₀/2) (haLo:0<aLo) (hB:0≤B) (hpstar:0<pstar):
    ∃ eps:ℝ,0<eps ∧ ∃ K:ℕ,0<K ∧ ∃ zeta:ℝ,0<zeta ∧
    ∃ θ:ℝ,0<θ ∧ ∃ etaEmax:ℝ,0<etaEmax ∧ ∀ etaE:ℝ,0<etaE→etaE≤etaEmax→∀ d:ℕ,1≤d→∃ N:ℕ,1≤N ∧
    ∀ omega t rho:ℝ,omega₀≤omega → t₀≤t → rho₀≤rho → rho≤1 → (((r+1)+3:ℕ):ℝ)*t≤1 →
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    N≤Fintype.card V→(Fintype.card U:ℝ)≤Fintype.card V→ omega*Fintype.card V≤(Fintype.card U:ℝ)→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V),
    (∀ x,(1/2+gamma/2)*Fintype.card V≤(P.degree x:ℝ))→
    (∀ x,|(P.degree x:ℝ)-2*Fintype.card U/rho|≤eps*Fintype.card V)→
    ∀ (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color),
    (∀ u,q u g=t)→(∀ u,s u j=(((r+1)+3:ℕ):ℝ)*t)→
    ∀ (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop),
    MarkedRowsWithSpokes P π d ((r+1)+11) Finset.univ (rho*((((r+1)+3:ℕ):ℝ)*t)/2) (rho*t/2)
      q s g j (eps*Fintype.card V) σ H→
    MarkedIndicesWithSpokes π d ((r+1)+11) Finset.univ q s g j (eps*Fintype.card V) σ H→
    ∀ (D τ p k s₀:ℝ),(Fintype.card V:ℝ)/2≤D→D≤2*Fintype.card V→
    pstar≤p→pstar≤k→pstar≤s₀→p≤1→k≤1→s₀≤1→
    ∀ weight:(Fin (r+4+1)→V)→ℝ,SuccessorSequenceWeightConditions P π (3*d) D τ aLo B weight→
    MarkedLocalConfigurationsWithSpokes r P π d Finset.univ (2*β) (2*β) σ H→
    MarkedLocalSpokeLoadsWithSpokes P π d (r+4) D p k s₀ weight (θ/2) σ H→
    (∀ x u,¬(H false x u∧H true x u))→
    (∀ u x z,H false x u→H true z u→x≠π z)→
    ∀ (I T:Finset V) (J W:Finset U),T⊆I→W⊆J→
    (∀ x,π x∈I↔x∈I)→(∀ x,π x∈T↔x∈T)→
    (I.card:ℝ)≤zeta*Fintype.card V→(J.card:ℝ)≤zeta*Fintype.card V→
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E₀=>e.val.1
    let head:=fun e:E₀=>e.val.2
    let ktail:=fun e:E₁=>e.val.1
    let khead:=fun e:E₁=>e.val.2
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)
    ∀ (DA:Finset (E₀⊕E₁)) (DS₀:Finset (V×U)),
    (DA.card:ℝ)≤etaE^2*(Fintype.card V:ℝ)^2→(DS₀.card:ℝ)≤etaE^2*(Fintype.card V:ℝ)^2→
    (∀ a∈DA,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I)→
    (∀ x,((DA.filter (fun a=>x=Sum.elim tail ktail a∨x=Sum.elim head khead a)).card:ℝ)≤etaE^2*Fintype.card V)→
    (∀ z∈DS₀,z.1∈I∧z.2∈J∧z∈S)→
    (∀ x,((DS₀.filter (fun z=>x=z.1)).card:ℝ)≤etaE^2*Fintype.card V)→
    (∀ u,((DS₀.filter (fun z=>z.2=u)).card:ℝ)≤etaE^2*Fintype.card V)→
    let CA:=(Finset.univ.filter (fun a:E₀⊕E₁=>Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I))\DA
    let CS:=(S.filter (fun z=>z.1∈I∧z.2∈J))\DS₀
    MarkedRemainderDivisible tail head ktail khead (H true) Finset.univ S (r+4)→
    MarkedRemainderDivisible tail head ktail khead (H true) CA CS (r+4)→
    let KA:=CA.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
    let KS:=CS.filter (fun z=>z.1∈T∨z.2∈W)
    ∃ M:Finset (MarkedWheel tail head ktail khead (r+4) π (3*d) (H false) (H true)),
    (∀ X∈M,∀ Y∈M,X≠Y→Disjoint (markedWheelPhysicalResources X) (markedWheelPhysicalResources Y))∧
    (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=
      (markedFiniteResources tail head ktail khead π DA DS₀).filter (markedStarResource T W)∧
    (∀ x,((markedPackingRimGraph M).degree x:ℝ)≤24*etaE*Fintype.card V)∧
    (∀ x,((Finset.univ.filter (markedPackingSpokes M x)).card:ℝ)≤6*etaE*Fintype.card V)∧
    (∀ u,((Finset.univ.filter (fun x=>markedPackingSpokes M x u)).card:ℝ)≤3*(r+5)*etaE*Fintype.card V)∧
    M.biUnion markedWheelArcs⊆Finset.univ\KA∧M.biUnion markedWheelSpokePairs⊆S\KS∧
    let DR:=markedSampleArcSetGraph P π d σ (KA∪M.biUnion markedWheelArcs)
    let DS:=markedFiniteSpokeGraph (KS∪M.biUnion markedWheelSpokePairs)
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E₀':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let E₁':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let tail':=fun e:E₀'=>e.val.1
    let head':=fun e:E₀'=>e.val.2
    let ktail':=fun e:E₁'=>e.val.1
    let khead':=fun e:E₁'=>e.val.2
    ∃ M_D:Finset (MarkedWheel tail' head' ktail' khead' (r+4) π (3*d) (H' false) (H' true)),
      (∀ X∈M_D,∀ Y∈M_D,X≠Y→Disjoint (markedWheelPhysicalResources X) (markedWheelPhysicalResources Y)) ∧
      (∀ x∉I,(markedPackingRimGraph M_D).degree x≤2*W.card+T.card*(4*(K+4))+2*T.card) ∧
      (∀ x∉I,(Finset.univ.filter (markedPackingSpokes M_D x)).card≤W.card+T.card*(K+4)) ∧
      (∀ u∉W,(Finset.univ.filter (fun x=>markedPackingSpokes M_D x u)).card≤T.card*(r+5)) ∧
      (M_D.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=∅ ∧
      (M_D.biUnion markedWheelPhysicalResources).filter (markedStarResource (I\T) (J\W))=∅ ∧
      (∀ X∈M_D,(X.2.val∈W∧markedWheelRows X⊆Iᶜ)∨
        (X.2.val∉J∧∃v∈T,markedWheelRows X⊆insert v Iᶜ∧v∈markedWheelRows X)) ∧
      (∀ a:E₀'⊕E₁',markedStarResource T W
          (Sum.inl (markedPhysicalEdge tail' head' ktail' khead' π a))→
          Sum.inl (markedPhysicalEdge tail' head' ktail' khead' π a)∈M_D.biUnion markedWheelPhysicalResources) ∧
      (∀ x u,H' false x u∨H' true x u→markedStarResource T W (Sum.inr (x,u))→
          Sum.inr (x,u)∈M_D.biUnion markedWheelPhysicalResources) :=by
  have hr1:1≤r:=by omega
  let ps:=rho₀*t₀/2
  have hps:0<ps:=by dsimp [ps];positivity
  have hps1:ps≤1:=by dsimp [ps];nlinarith [mul_nonneg (sub_nonneg.mpr hrho₀1) ht₀.le]
  obtain ⟨betaP,epsP,deltaP,eta₀,hbetaP,hepsP,hdeltaP,heta₀,hpres⟩:=
    marked_sample_correction_star_packing r hr ps gamma omega₀ hps hps1 hg hg1 ho₀
  obtain ⟨epsD,hepsD,K,hK,zetaD,hzetaD,θ,hθ,deltaD,hdeltaD,hdeep⟩:=
    marked_reserved_sample_deep_cover_uniform r hr1 omega₀ t₀ rho₀ gamma eta ho₀ ht₀ ht₀1 hrho₀ hrho₀1 hg hg1 heta hetaSmall
      β aLo B pstar hβ hβt₀ haLo hB hpstar
  let eps:=min epsP epsD
  have heps:0<eps:=lt_min hepsP hepsD
  let zeta:=min zetaD (min (deltaP/2) (min (betaP/20) (deltaD/4)))
  have hzeta:0<zeta:=by dsimp [zeta];positivity
  have hzD:zeta≤zetaD:=min_le_left _ _
  have hzP:zeta≤deltaP/2:=(min_le_right _ _).trans (min_le_left _ _)
  have hzb:zeta≤betaP/20:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hzd:zeta≤deltaD/4:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let etaEmax:=min (eta₀/2) (deltaD/(100*(r+5)))
  have hmax:0<etaEmax:=by dsimp [etaEmax];positivity
  refine ⟨eps,heps,K,hK,zeta,hzeta,θ,hθ,etaEmax,hmax,?_⟩
  intro etaE hetaE hemax
  have heeta:etaE≤eta₀:=by have hh:=hemax.trans (min_le_left _ _);linarith only [hh,heta₀]
  have hedelta:etaE*(100*(r+5))≤deltaD:=
    (le_div_iff₀ (by positivity)).mp (hemax.trans (min_le_right _ _))
  have h24:24*etaE≤deltaD/4:=by
    have hr0:(0:ℝ)≤r:=Nat.cast_nonneg r
    nlinarith only [hedelta,hetaE,hr0]
  have h6:6*etaE≤deltaD/4:=by linarith only [h24,hetaE]
  have hcol:3*(r+5)*etaE≤deltaD/4:=by nlinarith only [hedelta,hdeltaD]
  intro d hd
  obtain ⟨NP,hNP,hpres⟩:=hpres etaE hetaE heeta d hd
  obtain ⟨ND,hND,hdeep⟩:=hdeep d hd
  refine ⟨max NP ND,hNP.trans (le_max_left _ _),?_⟩
  intro omega t rho hω htlo hρ hrho1 hst
  have ho:0<omega:=ho₀.trans_le hω
  have ht:0<t:=ht₀.trans_le htlo
  have hrho:0<rho:=hrho₀.trans_le hρ
  have hpsactual:ps≤rho*t/2:=by
    dsimp [ps];have hh:=mul_le_mul hρ htlo ht₀.le hrho.le;linarith
  have hpst:ps≤t:=by nlinarith only [hpsactual,hrho1,ht]
  intro V U Γ Color _ _ _ _ _ _ hn hUn hU P π hdeg hparent q s g j hq hs σ H hrows hindices
    D τ p k s₀ hDlo hDhi hp hk hs₀ hp1 hk1 hs₁ weight hw hconfigs hload hH hshift I T J W hTI hWJ hI hT hIsize hJsize
  intro E₀ E₁ tail head ktail khead S DA DS₀ hDAcard hDScard hDA hDAdeg hDS hDSrow hDScol CA CS houter hinner KA KS
  let n:=Fintype.card V
  have hn0:(0:ℝ)≤n:=Nat.cast_nonneg n
  have hepP:eps*n≤epsP*n:=mul_le_mul_of_nonneg_right (min_le_left _ _) hn0
  have hepD:eps*n≤epsD*n:=mul_le_mul_of_nonneg_right (min_le_right _ _) hn0
  have hIP:(I.card:ℝ)≤deltaP*n:=hIsize.trans (mul_le_mul_of_nonneg_right (by linarith only [hzP,hdeltaP]:zeta≤deltaP) hn0)
  have hJP:(J.card:ℝ)≤deltaP*n:=hJsize.trans (mul_le_mul_of_nonneg_right (by linarith only [hzP,hdeltaP]:zeta≤deltaP) hn0)
  have hIb:(I.card:ℝ)≤betaP*n/10:=by
    have hh:=mul_le_mul_of_nonneg_right hzb hn0
    have hb0:=mul_nonneg hbetaP.le hn0
    nlinarith only [hh,hIsize,hb0]
  have hJb:(J.card:ℝ)≤betaP*n/10:=by
    have hh:=mul_le_mul_of_nonneg_right hzb hn0
    have hb0:=mul_nonneg hbetaP.le hn0
    nlinarith only [hh,hJsize,hb0]
  have hOrd:ps≤rho*((((r+1)+3:ℕ):ℝ)*t)/2:=by
    have hr':(1:ℝ)≤((r+1)+3:ℕ):=by exact_mod_cast (show 1≤(r+1)+3 by omega)
    have hh:=mul_le_mul_of_nonneg_left hr' (mul_pos hrho ht).le
    nlinarith only [hh,hpsactual]
  have hSp:t≤(((r+1)+3:ℕ):ℝ)*t:=by
    have hr':(1:ℝ)≤((r+1)+3:ℕ):=by exact_mod_cast (show 1≤(r+1)+3 by omega)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hr' ht.le
  obtain ⟨M,hM,hexact,hR,hV,hC,hMA,hMS⟩:=hpres V U Γ Color ((le_max_left _ _).trans hn) ((mul_le_mul_of_nonneg_right hω hn0).trans hU) P π hdeg
    (rho*((((r+1)+3:ℕ):ℝ)*t)/2) (rho*t/2) q s g j hOrd hpsactual
    (fun u=>by rw [hq];exact hpst) (fun u=>by rw [hs];exact hpst.trans hSp) σ H
    (fun A B J hA hB hJ hsep=>(hrows A B J hA hB hJ hsep).trans_le hepP)
    (fun J hJ hsep=>(hindices J hJ hsep).trans_le hepP)
    I T J W hI hT hIb hJb hIP hJP DA DS₀ hDAcard hDScard hDA hDAdeg hDS hDSrow hDScol
  refine ⟨M,hM,hexact,hR,hV,hC,hMA,hMS,?_⟩
  apply hdeep omega t rho hω htlo hρ hrho1 hst V U Γ Color ((le_max_right _ _).trans hn) hUn hU P π hdeg
    (fun x=>(hparent x).trans hepD) q s g j hq hs σ H
    (fun A B J hA hB hJ hsep=>(hrows A B J hA hB hJ hsep).trans_le hepD)
    (fun J hJ hsep=>(hindices J hJ hsep).trans_le hepD)
    D τ p k s₀ hDlo hDhi hp hk hs₀ hp1 hk1 hs₁ weight hw hconfigs hload hH hshift I T J W hTI hWJ hI hT
    (hIsize.trans (mul_le_mul_of_nonneg_right hzD hn0))
    (hJsize.trans (mul_le_mul_of_nonneg_right hzD hn0))
    DA DS₀ hDA hDS houter hinner M hM hMA hMS hexact etaE hR hV hC
  · have h1:=mul_le_mul_of_nonneg_right hzd hn0
    have h2:=mul_le_mul_of_nonneg_right h24 hn0
    have h3:=mul_nonneg hdeltaD.le hn0
    nlinarith only [hIsize,h1,h2,h3]
  · have h1:=mul_le_mul_of_nonneg_right hzd hn0
    have h2:=mul_le_mul_of_nonneg_right h6 hn0
    have h3:=mul_nonneg hdeltaD.le hn0
    nlinarith only [hJsize,h1,h2,h3]
  · have h1:=mul_le_mul_of_nonneg_right hzd hn0
    have h2:=mul_le_mul_of_nonneg_right hcol hn0
    have h3:=mul_nonneg hdeltaD.le hn0
    nlinarith only [hIsize,h1,h2,h3]

end Oberwolfach
