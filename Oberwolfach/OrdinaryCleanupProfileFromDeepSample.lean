module

public import Oberwolfach.OrdinaryCleanupParentProfiles
public import Oberwolfach.OrdinaryRawHubParentPrior

@[expose] public section
/-! Construct the cleanup profile from the retained size-three tests and
    actual edit bounds on the same raw outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_cleanup_profile_from_deep_sample
    (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ) (X:Finset V) (Z:Finset U)
    (pR pH density tR tH L βe βh:ℝ) (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (hpR:0≤pR) (hpR1:pR≤1) (hpH:0≤pH) (hdensity:1/2≤density) (hs:∀u,s u j=pH)
    (hdis:Disjoint Q F) (hmin:∀v,density*X.card≤((X∩P.neighborFinset v).card:ℝ))
    (hrows:RawOrdinaryRows P π d 3 X pR s j tR raw)
    (hcolumns:RawOrdinaryDomainIndices F π d 3 Z pH j tH raw)
    (hrim:∀v,((changed ((rawWheelGraph P raw).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L)
    (hcol:∀u,((changed (Finset.univ.filter (fun v=>rawWheelSpokes π d raw j v u))
      (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤L)
    (hrow:∀v,((changed (Finset.univ.filter (rawWheelSpokes π d raw j v))
      (Finset.univ.filter (H v))).card:ℝ)≤L)
    (hext:βe*Fintype.card (V⊕U)+tR+3*L≤pR^2*pH*(2*density-1)*X.card)
    (hhub:βh*Fintype.card (V⊕U)+tH+2*L≤pH^2*Z.card):
    OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH L βe βh s j raw := by
  refine ⟨hpR,hpR1,hpH,hdensity,hs,hdis,hmin,?_,hcolumns,hrim,hcol,hrow,hext,hhub⟩
  intro S J hS hJ
  exact hrows S J (by omega) (by omega)

theorem ordinary_cleanup_profile_from_raw_parent_prior
    (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d k:ℕ) (X:Finset V) (Z:Finset U)
    (pR pH density tR tH L βe βh:ℝ) (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (endpointWeight:V→Sym2 (V⊕U)→ℝ) (triangleWeight:OrdinaryCycle P 3→ℝ)
    (α pstar βP ηP ηH βH c B tEnd:ℝ)
    (hpR:0≤pR) (hpR1:pR≤1) (hpH:0≤pH) (hdensity:1/2≤density) (hs:∀u,s u j=pH)
    (hdis:Disjoint Q F) (hmin:∀v,density*X.card≤((X∩P.neighborFinset v).card:ℝ))
    (hrim:∀v,((changed ((rawWheelGraph P raw).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L)
    (hcol:∀u,((changed (Finset.univ.filter (fun v=>rawWheelSpokes π d raw j v u))
      (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤L)
    (hrow:∀v,((changed (Finset.univ.filter (rawWheelSpokes π d raw j v))
      (Finset.univ.filter (H v))).card:ℝ)≤L)
    (hext:βe*Fintype.card (V⊕U)+tR+3*L≤pR^2*pH*(2*density-1)*X.card)
    (hhub:βh*Fintype.card (V⊕U)+tH+2*L≤pH^2*Z.card)
    (hprior:OrdinaryRawHubParentPrior d k P F X Z π j s endpointWeight triangleWeight
      α pstar βP ηP ηH βH c B pR pH tEnd tR tH raw):
    OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH L βe βh s j raw := by
  exact ordinary_cleanup_profile_from_deep_sample P Q F H π d X Z pR pH density tR tH L βe βh s j raw
    hpR hpR1 hpH hdensity hs hdis hmin hprior.2.2.1 hprior.2.2.2 hrim hcol hrow hext hhub
end Oberwolfach
