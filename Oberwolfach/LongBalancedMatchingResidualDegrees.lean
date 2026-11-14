module

public import Oberwolfach.LongSelectedOrientedHostComplementProof
public import Oberwolfach.LongSelectedOrientedHostSpokesProof
public import Oberwolfach.LongSelectedOrientedBalancedDegreesProof
public import Oberwolfach.ExpandedClassCorrectionArcs

@[expose] public section
/-! One balanced physical orientation supplies the host hypotheses, and the
same matching and complement then supply the exact residual degree identities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longBalancedMatchingResidualFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem long_balanced_matching_residual_degrees
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hU:0<Fintype.card U) (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σ (Sum.inr e))) false) t)
    (H:Finset U) (A:Finset (Fin n)) (Kbad Used DelG:SimpleGraph (Fin n)) (absorber:U→Finset (Fin n))
    (δ:ℝ) (Sclass:SimpleGraph (Fin n)) (Mhost:Fin n→Fin n→ℕ) (Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop) (ρ₀ θ δglobal:ℝ)
    (hd:2≤d) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hphysical:∀x y,Mhost x y+Mhost y x=if Sclass.Adj x y then 1 else 0)
    (hbalance:∀v,(∑w,Mhost v w)=Fintype.card U ∧ (∑w,Mhost w v)=Fintype.card U)
    (hSP:Sclass≤P)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph P σ {0,1,2,3,4}) (fun e=>(σ (Sum.inl e)).2) Mhost≤DelG)
    (hUsedAvoid:∀x y,Used.Adj x y→¬DelG.Adj x y):
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let e:{z // z∈T}↪_:=Function.Embedding.subtype _
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),
    LongSelectedOrientedSourceWithHostCompletion hU F P π d m ℓ raw t Jret σ H A Kbad Used DelG absorber δ
      (fun x y=>Mhost x y=1) Extra ρ₀ θ δglobal M →
    LongSelectedOrientedSourceWithBalancedDegrees hU F P π d m ℓ raw t Jret σ H A Kbad Used DelG absorber δ
      Mhost Extra ρ₀ θ δglobal M:=by
  intro raw T e M hsource
  have hhost:∀x y,Mhost x y=1→P.Adj x y:=by
    intro x y h
    exact hSP (balanced_direction_is_host_edge Sclass Mhost hphysical x y h)
  have hsample:∀x y,rawMixedPhysicalArc P π d raw x y→¬DelG.Adj x y→Mhost x y=1:=by
    intro x y h hDel
    have hh:=approximate_arc_sampled_class P π d σ x y h
    have hdec6:instDecidableEqFin 6=longBalancedMatchingResidualFin 6:=Subsingleton.elim _ _
    try rw [hdec6] at hh
    exact sampled_class_arc_follows_corrected_orientation _ DelG _ Mhost hcorrect x y hh.1 hh.2 hDel
  have hc:=long_selected_oriented_host_complement hU F hF P π d m ℓ raw t Jret σ H A Kbad Used DelG absorber δ
    (fun x y=>Mhost x y=1) Extra ρ₀ θ δglobal hd hhost hUsedAvoid hsample M hsource
  have hs:=long_selected_oriented_host_spokes hU F hF P π d m ℓ raw t Jret σ H A Kbad Used DelG absorber δ
    (fun x y=>Mhost x y=1) Extra ρ₀ θ δglobal hd hnoshort M hc
  exact long_selected_oriented_balanced_degrees hU F hF P π d m ℓ raw t Jret σ H A Kbad Used DelG absorber δ
    Sclass Mhost Extra ρ₀ θ δglobal hd hnoshort hphysical hbalance M hs
end Oberwolfach
