module

public import Oberwolfach.OrdinarySelectedPostmatchingEmbeddingTrackedResult
public import Oberwolfach.OrdinaryFixedPostmatchingInputs
public import Oberwolfach.OrdinaryFixedTargetMatchingInputs
public import Oberwolfach.OrdinaryEmptyRetentionOutcome
public import Oberwolfach.OrdinaryPackagedCapacityFromMatching
public import Oberwolfach.OrdinaryPackagedForcedLoadFromBoundary
public import Oberwolfach.OrdinaryInnerTargetCapacity
public import Oberwolfach.OrdinaryMatchingBalanceBoundary

@[expose] public section
/-! The remaining numeric inputs for placing the matched complements on the
actual edited target, with their matching and old images retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryFixedPostmatchingEmbeddingShape
    (m d:ℕ) (hm:7≤m) (hd:2≤d) (θ δ:ℝ) (hθ:0<θ) (hδ:0<δ):Prop :=
    ∃N:ℕ,∀{n K:ℕ},N≤n→0<n→0<K→
    ∀(U:Type) [Fintype U] [DecidableEq U],Fintype.card U≤n→
    ∀(F₀:U→SimpleGraph (Fin n)) (hF₀:∀u,(F₀ u).IsRegularOfDegree 2)
    (Allowed:Set ℕ), (∀u,AllowedCycleLengths (F₀ u) Allowed)→
    ∀(i₀:Fin K) (rsv:ℝ),0≤ rsv→ rsv≤1/100→θ≤1/100→
    OrdinaryClassReserveBound F₀ hF₀ i₀ rsv→
    ∀(Cres:∀u,Finset (F₀ u).ConnectedComponent),
      (∀u (c:↥(Cres u)),Fintype.card c.val=i₀.val+1)→
      (∀u,((i₀.val+1:ℕ):ℝ)*(Cres u).card=rsv*n)→
    ∀(π:Equiv.Perm (Fin n)),(∀x l,0<l→l<2*d+1→(π^l) x≠x)→
    ∀(P S:SimpleGraph (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (Inner:Finset (Fin n)) (Hubs:Finset U) (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×U)))
    (lamMatch a γ ζret κ b z ρ₀ smin lamList p:ℝ),
    0≤ζret→0≤lamMatch+γ*(1-θ+lamMatch)→lamMatch+γ*(1-θ+lamMatch)≤θ/8→
    max a γ≤κ→
    1/(8*(d:ℝ))+((m:ℝ)+1)*(d:ℝ)*ζret+(lamMatch+γ*(1-θ+lamMatch))≤(δ/8)/2→
    2*θ+δ/8+((m:ℝ)+2)*κ≤δ→
    0<ρ₀→0<smin→0≤b→
    let αCap:=5*ρ₀*smin^2/128;
    16/(d:ℝ)+16*κ+16*b/αCap+4*z≤θ/8→
    (Inner.card:ℝ)≤z*n→ρ₀*n≤4*(Fintype.card U:ℝ)→
    (Hubs.card:ℝ)≤αCap*n→(n:ℝ)^(3/4:ℝ)≤αCap*n→b≤αCap/16→b≤δ/8→
    4/(d:ℝ)≤δ/16→4*(n:ℝ)^(3/4:ℝ)≤δ*n/16→2*((max a γ)*n)≤δ*n/8→
    (Hubs.card:ℝ)≤δ*n/2→0<lamList→lamList/2≤1→δ≤((lamList/2)/100)^2→
    100/(lamList/2)≤(n:ℝ)→2/Real.sqrt δ≤(n:ℝ)→
    (∀u,(∑g:Bool,ordinaryAssignedMarkedProbability F₀ hF₀ K θ ((m:ℝ)+1) u g)≤1/8)→
    (∀u g,|rawIntervalHubStartCount π d g (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σ (Sum.inr e))) u-
      (n:ℝ)*ordinaryAssignedMarkedProbability F₀ hF₀ K θ ((m:ℝ)+1) u g/d|<(n:ℝ)^(3/4:ℝ)/d)→
    OrdinaryZeroRetentionEvent π d false σ→OrdinaryBoundaryStartEvent π d σ→
    ∀s:U→Bool→ℝ,OrdinaryReservedCompletionTests P π d p smin s σ→
    OrdinaryFixedPostmatchingInputs F₀ hF₀ Cres i₀ rsv θ lamMatch a γ m d π P S σ Inner Hubs Kabs lamList b→
    let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4}
    let Conf:=permutationConflictGraph π (3*d)
    let Ref:=longPhysicalStateGraph P σ {0}\Conf
    let Protect:=ordinaryMatchingProtect Ref Inner Kabs
    let Del:=Sample\S
    let J:=ordinaryEmptyRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false);
    OrdinarySelectedPostmatchingEmbeddingTrackedResult F₀ hF₀ Cres i₀ rsv θ lamMatch a γ m d π P Del S Protect Sample Ref Conf σ 0 J
      Inner Hubs (ordinaryReservoirSpokeLabels Kabs) δ
end Oberwolfach
