module

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

theorem ordinary_general_margins_from_capacity
    (m:ℕ) (Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (p εsup τ ν η ell κ ζ βe rate:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W (m+1) (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)))
    (σ:Sym2 (V⊕U)→Bool)
    (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W (m+1) (η*Fintype.card (V⊕U))
      (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) D σ)
    (hp:0<p) (hp1:p≤1) (hτ:0≤τ) (hκ:0<κ) (hκ1:κ≤1) (hζ:0<ζ)
    (hε:εsup≤p^2/4) (hsupport:τ+ν≤p^2/4)
    (hclass:τ+ν+ell≤ζ*κ*p/4) (hblock:ν+η≤ζ*κ*p/4)
    (hpκ:p≤4*ζ*κ) (hsqrt:20*Real.sqrt (2*p)≤ζ*κ/2)
    (horder:2≤ζ*κ*p*Fintype.card (V⊕U)/4)
    (hY:∀j:{u:U // u∉Z},κ*Fintype.card (V⊕U)≤((ordinaryBoundaryHubSet H Z X j).card:ℝ))
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
    OrdinaryGeneralRootFirstMargins m Q Qfactor F H Hfactor X T Z W
      (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U))
      D σ O p (2*p) ζ εsup βe (rate*Fintype.card (V⊕U)) :=by
  let n:ℝ:=Fintype.card (V⊕U)
  have hn:0≤n:=by dsimp [n];positivity
  obtain ⟨hdeg,hpair,hmargin⟩:=ordinary_root_first_selection_margins p εsup τ ν η ell κ ζ n
    hp hp1 hκ hζ hn hε hsupport hclass hblock hpκ hsqrt horder
  have hnκ:κ*n≤n:=by nlinarith [hκ1,hn]
  let K:=O.context
  let C:=ordinaryRootFirstPrecoverPrior Q F H X T Z W (m+1) (η*n) (ell*n) (τ*n) K σ
  let J:=ordinaryPhysicalGraph (wheelFamilyRim O.cleanup.wheels) (wheelFamilySpokes O.cleanup.wheels)
  let E:=ordinaryPhysicalGraph K.cover.rim K.cover.spokes
  let Klocal:=J⊔spanningRestriction E (ordinaryInnerVertices X Z)
  have hf:=ordinary_root_first_precover_selection_data Q Qfactor F H Hfactor X T Z W (m+1)
    (η*n) (ell*n) (τ*n) (ν*n) D σ O (mul_nonneg hτ hn) hbase
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
  refine ⟨hbase,hdeg,hpair,(fun j=>(hmargin _ (hY j)).1),(hmargin n hnκ).1,
    (fun j=>(hmargin _ (hY j)).2),(hmargin n hnκ).2,Dmax,Kcap,hKcap,hDmax,Lconf,hLconf,hF,?_,?_⟩
  · exact hcompletion'
  · linarith only [hcost]
end Oberwolfach
