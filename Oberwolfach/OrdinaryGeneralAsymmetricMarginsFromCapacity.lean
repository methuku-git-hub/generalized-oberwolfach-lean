module

public import Oberwolfach.OrdinaryGeneralRootFirstAsymmetricMargins
public import Oberwolfach.OrdinaryRootFirstPrecoverSelectionDataSampledCover
public import Oberwolfach.OrdinarySampledCoverDegree
public import Oberwolfach.OrdinaryGeneralRootFirstMargins
public import Oberwolfach.OrdinaryRootFirstSelectionMargins
public import Oberwolfach.OrdinaryBoundaryRowTotalBound
public import Oberwolfach.OrdinaryRootFirstPrecoverSelectionData
public import Oberwolfach.BoundaryDegreeAfterPacking

@[expose] public section
/-! Turn the uniform general-wheel capacity bounds into the actual
    root-first completion margins on any supported fresh sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_general_asymmetric_margins_from_capacity
    (m:ℕ) (Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (p εsup τ ν η ell κh κinner ζh ζe θmatch ninner βe rate δsample:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W (m+1) (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)))
    (σ:Sym2 (V⊕U)→Bool)
    (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W (m+1) (η*Fintype.card (V⊕U))
      (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) D σ)
    (hp:0<p) (hp1:p≤1) (hτ:0≤τ) (hκh:0≤κh) (hκinner:0≤κinner) (hζh:0≤ζh) (hζe:0≤ζe) (hθmatch:0<θmatch)
    (hθmatchh:θmatch≤ζh*κh) (hθmatche:θmatch≤ζe*κinner)
    (hε:εsup≤p^2/4) (hsupport:τ+ν≤p^2/4)
    (hclass:τ+ν+(p*ell+δsample)≤θmatch*p/4) (hblock:ν+η≤θmatch*p/4)
    (hpκ:p≤4*θmatch) (hsqrt:20*Real.sqrt (2*p)≤θmatch/2)
    (horder:2≤θmatch*p*Fintype.card (V⊕U)/4)
    (hY:∀j:{u:U // u∉Z},κh*Fintype.card (V⊕U)≤((ordinaryBoundaryHubSet H Z X j).card:ℝ))
    (hinner:κinner*Fintype.card (V⊕U)≤ninner)
    (hcover:OrdinarySampledCoverDegreeGood (ordinaryPhysicalGraph D.rim D.spokes) p δsample σ)
    (hsample:BoundaryReserveSupportGood (ordinaryBoundaryGraph Q H X Z) p εsup σ)
    (hbase:ordinaryPhysicalGraph Qfactor Hfactor≤spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z))
    (Kcap Dmax:ℕ) (hKcap:0<Kcap) (hDmax:(2*p)*Fintype.card (V⊕U)≤(Dmax:ℝ))
    (Lconf:ℝ) (hLconf:0≤Lconf) (hF:∀v,(F.degree v:ℝ)≤Lconf)
    (hT:(T.card:ℝ)≤(βe/2)*Fintype.card (V⊕U))
    (hcompletion:((Fintype.card (V⊕U)*Dmax*(m+1):ℕ):ℝ)/(Kcap:ℝ)+
      (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*((2*p)*Fintype.card (V⊕U))+2*((Kcap+Dmax:ℕ):ℝ))+
      (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax < (βe/2)*Fintype.card (V⊕U)-3*(ν*Fintype.card (V⊕U)))
    (hcost:ν*Fintype.card (V⊕U)+η*Fintype.card (V⊕U)+2*((2*p)*Fintype.card (V⊕U))+
      ((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ)≤rate*Fintype.card (V⊕U)):
    OrdinaryGeneralRootFirstAsymmetricMargins m Q Qfactor F H Hfactor X T Z W
      (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U))
      D σ O p (2*p) ζh ζe ninner εsup βe (rate*Fintype.card (V⊕U))
      (p*(ell*Fintype.card (V⊕U))+δsample*Fintype.card (V⊕U)) :=by
  let n:ℝ:=Fintype.card (V⊕U)
  have hn:0≤n:=by dsimp [n];positivity
  obtain ⟨hdeg,hpair,hmargin⟩:=ordinary_root_first_selection_margins p εsup τ ν η (p*ell+δsample) 1 θmatch n
    hp hp1 (by norm_num) hθmatch hn hε hsupport (by simpa using hclass) (by simpa using hblock)
    (by simpa using hpκ) (by simpa using hsqrt) (by simpa only [mul_one,n] using horder)
  let K:=O.context
  let C:=ordinaryRootFirstPrecoverPrior Q F H X T Z W (m+1) (η*n) (ell*n) (τ*n) K σ
  let J:=ordinaryPhysicalGraph (wheelFamilyRim O.cleanup.wheels) (wheelFamilySpokes O.cleanup.wheels)
  let E:=ordinaryPhysicalGraph K.cover.rim K.cover.spokes
  let Klocal:=J⊔spanningRestriction E (ordinaryInnerVertices X Z)
  have hf:=ordinary_root_first_precover_selection_data_sampled_cover Q Qfactor F H Hfactor X T Z W (m+1)
    (η*n) (ell*n) (τ*n) (ν*n) D σ O (mul_nonneg hτ hn) hbase (p*(ell*n)+δsample*n)
    (ordinary_sampled_cover_boundary_degree Q F H X T Z W (m+1) (η*n) (ell*n) p δsample D σ hp.le hcover)
  have hb:=boundary_degree_after_packing (ordinaryBoundaryGraph Q H X Z) C J σ p εsup (τ*n+ν*n)
    hp.le hsample hf.1 hf.2.2.2.1
  let Q₂:=ordinaryRootFirstCleanRemainderRim Q F H X T Z W (m+1) (η*n) (ell*n) (τ*n) (ν*n) D σ O
  let H₂:=ordinaryRootFirstCleanRemainderSpokes Q F H X T Z W (m+1) (η*n) (ell*n) (τ*n) (ν*n) D σ O
  have hQdeg:∀w:V⊕U,(ordinaryBoundaryGraph Q₂ H₂ X Z).degree w≤Dmax:=by
    intro w
    have hsub:((ordinaryBoundaryGraph Q₂ H₂ X Z).degree w:ℝ)≤
        ((((ordinaryBoundaryGraph Q H X Z\C)\J).degree w):ℝ):=by
      exact_mod_cast SimpleGraph.degree_le_of_le hf.2.2.1 (v:=w)
    have hbound:=hsub.trans ((hb w).trans (hdeg.trans hDmax))
    exact_mod_cast hbound
  have hrows:=ordinary_boundary_row_total_bound Q₂ H₂ X Z Dmax hQdeg
  have hrows':((Fintype.card (Σi:{v:V // v∉X},ordinaryBoundaryRowSet H₂ X Z i)*(m+1):ℕ):ℝ)≤
      ((Fintype.card (V⊕U)*Dmax*(m+1):ℕ):ℝ):=by
    exact_mod_cast Nat.mul_le_mul_right (m+1) hrows
  have hfrac:=div_le_div_of_nonneg_right hrows' (show 0≤(Kcap:ℝ) by positivity)
  have hcompletion':((Fintype.card (Σi:{v:V // v∉X},ordinaryBoundaryRowSet H₂ X Z i)*(m+1):ℕ):ℝ)/(Kcap:ℝ)+
      (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*((2*p)*Fintype.card (V⊕U))+2*((Kcap+Dmax:ℕ):ℝ))+
      (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax < βe*Fintype.card (V⊕U)-3*(ν*Fintype.card (V⊕U))-T.card:=by
    linarith only [hfrac,hcompletion,hT]
  have htargetY (j:{u:U // u∉Z}):θmatch*(p*n)≤ζh*(p*(ordinaryBoundaryHubSet H Z X j).card):=by
    have h1:=mul_le_mul_of_nonneg_right hθmatchh hn
    have h2:=mul_le_mul_of_nonneg_left (hY j) hζh
    have hx:θmatch*n≤ζh*(ordinaryBoundaryHubSet H Z X j).card:=by nlinarith only [h1,h2]
    have h3:=mul_le_mul_of_nonneg_left hx hp.le
    nlinarith only [h3]
  have htargetE:θmatch*(p*n)≤ζe*(p*ninner):=by
    have h1:=mul_le_mul_of_nonneg_right hθmatche hn
    have h2:=mul_le_mul_of_nonneg_left hinner hζe
    have hx:θmatch*n≤ζe*ninner:=by nlinarith only [h1,h2]
    have h3:=mul_le_mul_of_nonneg_left hx hp.le
    nlinarith only [h3]
  have hbaseMargin:=hmargin n (by simpa using hn)
  have hscaleY:∀j:{u:U // u∉Z},τ*n+ν*n+(p*(ell*n)+δsample*n)≤ζh*(p*(ordinaryBoundaryHubSet H Z X j).card):=by
    intro j
    have hh:=hbaseMargin.1.trans (htargetY j)
    nlinarith only [hh]
  have hscaleE:τ*n+ν*n+(p*(ell*n)+δsample*n)≤ζe*(p*ninner):=by
    have hh:=hbaseMargin.1.trans htargetE
    nlinarith only [hh]
  refine ⟨hbase,hdeg,hpair,hscaleY,hscaleE,
    (fun j=>hbaseMargin.2.trans (htargetY j)),hbaseMargin.2.trans htargetE,
    Dmax,Kcap,hKcap,hDmax,Lconf,hLconf,hF,?_,?_⟩
  · exact hcompletion'
  · linarith only [hcost]
end Oberwolfach
