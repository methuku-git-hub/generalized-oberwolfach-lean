module

public import Oberwolfach.LongSelectedClassDynamicHostComplementProof
public import Oberwolfach.LongSelectedClassDynamicHostSpokesProof
public import Oberwolfach.LongSelectedClassDynamicBalancedDegreesProof

@[expose] public section
/-! Preserve the exact old packing and its dynamic repair through the host
complement, spoke identities and balanced residual degree calculation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance classDynamicBalancedMatchingFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem long_class_dynamic_balanced_matching_residual_degrees
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hU:0<Fintype.card U) (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (P Sclass:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σ (Sum.inr e))) false) t)
    (H:Finset U) (A:Finset (Fin n)) (Kbad:Finset (Sym2 (Fin n))→SimpleGraph (Fin n))
    (Used DelG:SimpleGraph (Fin n)) (absorber:U→Finset (Fin n)) (δ:ℝ)
    (Mhost:Fin n→Fin n→ℕ) (Dhost:Fin n→Fin n→Prop)
    (Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop) (ρ₀ θ δglobal:ℝ)
    (hd:2≤d) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hphysical:∀x y,Mhost x y+Mhost y x=if Sclass.Adj x y then 1 else 0)
    (hbalance:∀v,(∑w,Mhost v w)=Fintype.card U ∧ (∑w,Mhost w v)=Fintype.card U)
    (hDhost:∀x y,Dhost x y→Mhost x y=1) (hHostPhysical:∀x y,Dhost x y→P.Adj x y)
    (hUsedAvoid:∀x y,Used.Adj x y→¬DelG.Adj x y):
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    (∀x y,rawMixedPhysicalArc P π d raw x y→¬DelG.Adj x y→Dhost x y)→
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let e:{z // z∈T}↪_:=Function.Embedding.subtype _;
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),
    LongSelectedClassDynamicSourceHostCompletion hU F P π d m ℓ raw t Jret σ H A Sclass Kbad Used DelG absorber δ Dhost Extra ρ₀ θ δglobal M→
    LongSelectedClassDynamicSourceBalancedDegrees hU F P π d m ℓ raw t Jret σ H A Sclass Kbad Used DelG absorber δ Mhost Dhost Extra ρ₀ θ δglobal M:=by
  intro raw hsample T e M hsource
  have hc:=long_selected_class_dynamic_host_complement hU F hF P Sclass π d m ℓ raw t Jret σ H A Kbad Used DelG absorber δ
    Dhost Extra ρ₀ θ δglobal hd hHostPhysical hUsedAvoid hsample M hsource
  have hs:=long_selected_class_dynamic_host_spokes hU F hF P Sclass π d m ℓ raw t Jret σ H A Kbad Used DelG absorber δ
    Dhost Extra ρ₀ θ δglobal hd hnoshort M hc
  exact long_selected_class_dynamic_balanced_degrees hU F hF P π d m ℓ raw t Jret σ H A Kbad Used DelG absorber δ
    Sclass Mhost Dhost Extra ρ₀ θ δglobal hd hnoshort hDhost hphysical hbalance M hs
end Oberwolfach
