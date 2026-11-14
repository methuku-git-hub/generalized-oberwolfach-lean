module

public import Oberwolfach.OrdinaryAsymmetricMatchingScaleBounds
public import Oberwolfach.OrdinaryPhysicalInnerEndpointDomain
public import Oberwolfach.MarkedFixedVortexAmbientBounds

@[expose] public section
/-! The actual fixed vortex supplies the linear matching and physical-domain
scale bounds with constants chosen before the vortex scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε ρ₀:ℝ} (Q:Vortex U G D β ε m)

theorem ordinary_vortex_asymmetric_matching_scales
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:(Fintype.card V:ℝ)/2≤D)
    (hρ:0<ρ₀) (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hm:0<m) (i:ℕ) (hi:i<Q.length)
    (ζh ζe γ eCoeff:ℝ) (hζh:0<ζh) (hζe:0<ζe) (hγ:0<γ) (he:γ≤eCoeff):
    let A:=markedVortexInnerVertices Q i;
    let Z:=markedVortexInnerHubs Q i;
    let n:ℝ:=Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i);
    let κh:=γ*(1/4:ℝ)*ε;
    let κinner:=(1/4:ℝ)*ε;
    let c:=min (ζh*γ*(1/4:ℝ)) (ζe*(1/4:ℝ))/2;
    let θmatch:=c*ε;
    0<κh ∧ 0<κinner ∧ 0<c ∧ 0<θmatch ∧
    κh*n≤γ*A.card ∧ κinner*n≤(ordinaryPhysicalInnerDomain A Z).card ∧
    θmatch≤ζh*κh ∧ θmatch≤ζe*κinner ∧ γ*A.card≤(eCoeff*ε)*n:=by
  intro A Z n κh κinner c θmatch
  have hf:=marked_vortex_fixed_ambient_size_fields Q hreg hn hD hρ hρlo hρhi hβ hβ1 hε hm i hi
  have hV:Fintype.card (markedVortexVertexType Q i)=(Q.vertices i).card:=by
    change Fintype.card (Q.extendedVertices i)=(Q.vertices i).card
    rw [Fintype.card_coe,Q.extendedVertices_eq hi.le]
  have hAcard:A.card=(Q.vertices (i+1)).card:=by
    change (markedVortexInnerVertices Q i).card=_
    rw [(marked_vortex_inner_cardinalities Q i).1,Q.extendedVertices_eq (by omega : i+1≤Q.length)]
  have hupper:((A.card):ℝ)≤ε*Fintype.card (markedVortexVertexType Q i):=by
    rw [hAcard,hV]
    exact (Q.consecutive_size_bounds hε hm hi).2
  have hUV:(Fintype.card (markedVortexHubType Q i):ℝ)≤Fintype.card (markedVortexVertexType Q i):=by
    exact_mod_cast hf.2.2
  have hnEq:n=(Fintype.card (markedVortexVertexType Q i):ℝ)+Fintype.card (markedVortexHubType Q i):=by
    dsimp [n]
    simp
  have hn0:0≤n:=by dsimp [n];positivity
  have hlo:(1/4:ℝ)*ε*n≤(A.card:ℝ):=by
    rw [hnEq]
    have hh:=mul_le_mul_of_nonneg_left hUV hε.le
    nlinarith only [hf.1,hh]
  have hhi:(A.card:ℝ)≤ε*n:=by
    rw [hnEq]
    have hu:(0:ℝ)≤Fintype.card (markedVortexHubType Q i):=by positivity
    nlinarith [mul_nonneg hε.le hu]
  have hinside:(A.card:ℝ)≤(ordinaryPhysicalInnerDomain A Z).card:=by
    rw [ordinary_physical_inner_domain_card,Nat.cast_add]
    have hz:(0:ℝ)≤Z.card:=by positivity
    linarith only [hz]
  exact ordinary_asymmetric_matching_scale_bounds ζh ζe γ (1/4) ε n A.card
    (ordinaryPhysicalInnerDomain A Z).card eCoeff hζh hζe hγ (by norm_num) hε hn0 hlo hhi hinside he
end Oberwolfach
