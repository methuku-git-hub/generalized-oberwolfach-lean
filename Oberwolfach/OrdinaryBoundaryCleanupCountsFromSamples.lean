module

public import Oberwolfach.OrdinaryBoundaryParentCommon
public import Oberwolfach.OrdinaryBoundaryExtensionFromCommonSample
public import Oberwolfach.OrdinaryBoundaryHubPairFromCommonSample
public import Oberwolfach.OrdinaryBoundaryExtensionsSurvivePacking
public import Oberwolfach.OrdinaryBoundaryHubChoicesSurvive
public import Oberwolfach.OrdinaryBoundaryLocalEvents

@[expose] public section
/-! The original common-neighborhood sample and the fresh boundary sample
supply both extension counts needed for sparse outside-edge cleanup. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_cleanup_counts_from_common_and_fresh_samples
    (P Q₀ Q:SimpleGraph V) (F:SimpleGraph V) (H₀ H:V→U→Prop)
    (π:Equiv.Perm V) (d:ℕ) (X:Finset V) (Z:Finset U) (C:SimpleGraph (V⊕U))
    (pR pH p density tR tH L βe βh:ℝ)
    (hpR:0≤pR) (hpR1:pR≤1) (hpH:0≤pH) (hdensity:1/2≤density)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color) (σ:Sym2 (V⊕U)→Bool)
    (hs:∀u,s u j=pH) (hQsub:Q≤Q₀) (hQF:Disjoint Q₀ F)
    (hmin:∀v,density*X.card≤((X∩P.neighborFinset v).card:ℝ))
    (hrows:RawOrdinaryRows P π d 2 X pR s j tR raw)
    (hcols:RawOrdinaryDomainIndices F π d 3 Z pH j tH raw)
    (hrim:∀v,((changed ((rawWheelGraph P raw).neighborFinset v) (Q₀.neighborFinset v)).card:ℝ)≤L)
    (hcol:∀u,((changed (Finset.univ.filter (fun v=>rawWheelSpokes π d raw j v u))
      (Finset.univ.filter (fun v=>H₀ v u))).card:ℝ)≤L)
    (hrow:∀v,((changed (Finset.univ.filter (rawWheelSpokes π d raw j v))
      (Finset.univ.filter (H₀ v))).card:ℝ)≤L)
    (hmarginE:βe*Fintype.card (V⊕U)+tR+3*L≤pR^2*pH*(2*density-1)*X.card)
    (hmarginH:βh*Fintype.card (V⊕U)+tH+2*L≤pH^2*Z.card)
    (hinner:Disjoint C (spanningRestriction (ordinaryPhysicalGraph Q₀ H₀) (ordinaryInnerVertices X Z)))
    (hreserve:Disjoint C (retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ))
    (hkeep:ordinaryPhysicalGraph Q₀ H₀\C≤ordinaryPhysicalGraph Q H)
    (hevent:OrdinaryBoundaryExtensionGood Q₀ H₀ X βe p σ)
    (hhevent:OrdinaryBoundaryHubPairGood H₀ Z βh p σ):
    (∀u a c,p^3*βe*Fintype.card (V⊕U)/2≤
      (((X.filter (fun v=>H v u))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ)) ∧
    (∀a∉X,∀c∉X,Q.Adj a c→p^2*βh*Fintype.card (V⊕U)/2≤
      ((Z.filter (fun u=>H a u∧H c u)).card:ℝ)):=by
  have hcommon:=ordinary_boundary_parent_common_of_min_degree P X density hmin
  have hparent:=ordinary_boundary_parent_extensions_from_common_sample P Q₀ H₀ π d X pR pH (2*density-1)
    tR L βe hpR hpR1 hpH (by linarith) s j raw hs hrows hcommon hrim hcol hmarginE
  have hhparent:=ordinary_boundary_parent_hub_pairs_from_common_sample Q₀ Q F H₀ π d Z pH tH L βh j raw
    hQsub hQF hcols hrow hmarginH
  refine ⟨?_,?_⟩
  · exact ordinary_retained_extensions_survive_packing Q₀ Q H₀ H X Z C σ _ hinner hreserve hkeep hevent
  · apply ordinary_retained_hub_choices_survive_packing Q₀ Q H₀ H X Z C σ _ _ hinner hreserve hkeep hhevent
    intro a _ c _ hac
    exact hhparent a c hac
end Oberwolfach
