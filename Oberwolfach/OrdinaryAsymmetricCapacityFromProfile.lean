module

public import Oberwolfach.OrdinaryGeneralAsymmetricMarginsFromCapacity
public import Oberwolfach.OrdinaryGeneralRelativeHubConditionsFromCleanup
public import Oberwolfach.OrdinaryPhysicalInnerHost

@[expose] public section
/-! The cleanup profile supplies the hub-class sizes needed by the
asymmetric capacity calculation uniformly for every later cleanup outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_asymmetric_capacity_from_profile
    (m:ℕ) (P Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
    (pR pH density tR tH Ledit βe₀ βh₀ γ:ℝ) (raw:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH Ledit βe₀ βh₀ s j raw)
    (hX:X.Nonempty) (hscale:γ*X.card≤βe₀*Fintype.card (V⊕U))
    (p εsup τ ν η ell κh κinner ζh ζe θmatch ninner βe rate δsample:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W (m+1) (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)))
    (hp:0<p) (hp1:p≤1) (hτ:0≤τ) (hκh:0≤κh) (hκinner:0≤κinner) (hζh:0≤ζh) (hζe:0≤ζe) (hθ:0<θmatch)
    (hθh:θmatch≤ζh*κh) (hθe:θmatch≤ζe*κinner)
    (hε:εsup≤p^2/4) (hsupport:τ+ν≤p^2/4)
    (hclass:τ+ν+(p*ell+δsample)≤θmatch*p/4) (hblock:ν+η≤θmatch*p/4)
    (hpθ:p≤4*θmatch) (hsqrt:20*Real.sqrt (2*p)≤θmatch/2)
    (horder:2≤θmatch*p*Fintype.card (V⊕U)/4)
    (hκscale:κh*Fintype.card (V⊕U)≤γ*X.card)
    (hinner:κinner*Fintype.card (V⊕U)≤ninner)
    (Kcap Dmax:ℕ) (hKcap:0<Kcap) (hDmax:(2*p)*Fintype.card (V⊕U)≤(Dmax:ℝ))
    (Lconf:ℝ) (hLconf:0≤Lconf) (hF:∀v,(F.degree v:ℝ)≤Lconf)
    (hT:(T.card:ℝ)≤(βe/2)*Fintype.card (V⊕U))
    (hcompletion:((Fintype.card (V⊕U)*Dmax*(m+1):ℕ):ℝ)/(Kcap:ℝ)+
      (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*((2*p)*Fintype.card (V⊕U))+2*((Kcap+Dmax:ℕ):ℝ))+
      (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax < (βe/2)*Fintype.card (V⊕U)-3*(ν*Fintype.card (V⊕U)))
    (hcost:ν*Fintype.card (V⊕U)+η*Fintype.card (V⊕U)+2*((2*p)*Fintype.card (V⊕U))+
      ((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ)≤rate*Fintype.card (V⊕U)):
    ∀σ (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W (m+1) (η*Fintype.card (V⊕U))
      (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) D σ),
    BoundaryReserveSupportGood (ordinaryBoundaryGraph Q H X Z) p εsup σ→
    OrdinarySampledCoverDegreeGood (ordinaryPhysicalGraph D.rim D.spokes) p δsample σ→
    OrdinaryGeneralRootFirstAsymmetricMargins m Q (spanningRestriction Q X) F H
      (fun v u=>H v u∧v∈X∧u∈Z) X T Z W
      (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U))
      D σ O p (2*p) ζh ζe ninner εsup βe (rate*Fintype.card (V⊕U))
      (p*(ell*Fintype.card (V⊕U))+δsample*Fintype.card (V⊕U)):=by
  have hc:=ordinary_general_relative_hub_conditions_from_cleanup P Q F H X Z π d j s γ
    pR pH density tR tH Ledit βe₀ βh₀ raw profile hX hscale
  have hY:∀u:{u:U // u∉Z},κh*Fintype.card (V⊕U)≤((ordinaryBoundaryHubSet H Z X u).card:ℝ):=
    fun u=>hκscale.trans (hc.1 u)
  have hbase:ordinaryPhysicalGraph (spanningRestriction Q X) (fun v u=>H v u∧v∈X∧u∈Z)≤
      spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z):=by
    rw [ordinary_physical_inner_host]
  intro σ O hsample hcover
  exact ordinary_general_asymmetric_margins_from_capacity m Q (spanningRestriction Q X) F H
    (fun v u=>H v u∧v∈X∧u∈Z) X T Z W p εsup τ ν η ell κh κinner ζh ζe θmatch ninner βe rate δsample
    D σ O hp hp1 hτ hκh hκinner hζh hζe hθ hθh hθe hε hsupport hclass hblock hpθ hsqrt horder hY hinner
    hcover hsample hbase Kcap Dmax hKcap hDmax Lconf hLconf hF hT hcompletion hcost
end Oberwolfach
