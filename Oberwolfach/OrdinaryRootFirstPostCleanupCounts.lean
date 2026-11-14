module

public import Oberwolfach.OrdinaryRootFirstCleanupCountsFromProfile
public import Oberwolfach.OrdinaryRootFirstFinishData
public import Oberwolfach.OrdinaryInnerExtensionsAfterLocalCover

@[expose] public section
/-! The post-packing common extensions survive the cleanup, losing at
most three times its physical maximum-degree bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_root_first_post_cleanup_counts
    (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
    (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t ν:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W r η ell) (σ:Sym2 (V⊕U)→Bool)
    (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W r η ell t ν D σ) (ht:0≤t)
    (pR pH p density tR tH L βe₀ βh₀ βe βh:ℝ) (s:U→Color→ℝ) (j:Color)
    (raw:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH L βe₀ βh₀ s j raw)
    (hmE:βe*Fintype.card (V⊕U)+3*max η ell≤βe₀*Fintype.card (V⊕U))
    (hmH:βh*Fintype.card (V⊕U)+2*ell≤βh₀*Fintype.card (V⊕U))
    (hevent:OrdinaryBoundaryExtensionGood (Q\O.context.cover.rim)
      (fun v u=>H v u∧¬O.context.cover.spokes v u) X βe p σ)
    (hhevent:OrdinaryBoundaryHubPairGood (fun v u=>H v u∧¬O.context.cover.spokes v u) Z βh p σ):
    let Q₂:=ordinaryRootFirstCleanRemainderRim Q F H X T Z W r η ell t ν D σ O;
    let H₂:=ordinaryRootFirstCleanRemainderSpokes Q F H X T Z W r η ell t ν D σ O;
    ∀u∈Z,∀a∈X,∀c∈X,(p^3*βe/2)*Fintype.card (V⊕U)-3*ν≤
      (((X.filter (fun v=>H₂ v u))∩Q₂.neighborFinset a∩Q₂.neighborFinset c).card:ℝ):=by
  intro Q₂ H₂
  let K:=O.context
  let Q₁:=(Q\K.cover.rim)\ordinaryRootFirstPackingRim Q F H X T Z W r η ell t K
  let H₁:=fun v u=>(H v u∧¬K.cover.spokes v u)∧¬ordinaryRootFirstPackingSpokes Q F H X T Z W r η ell t K v u
  let R:=wheelFamilyRim O.cleanup.wheels
  let S:=wheelFamilySpokes O.cleanup.wheels
  have hr:K.reserve=retainedGraph (ordinaryBoundaryGraph (Q\K.cover.rim)
      (fun v u=>H v u∧¬K.cover.spokes v u) X Z) σ:=by
    change O.context.reserve=retainedGraph (ordinaryBoundaryGraph (Q\O.context.cover.rim)
      (fun v u=>H v u∧¬O.context.cover.spokes v u) X Z) σ
    rw [O.cover_eq];exact O.reserve_eq
  have hcounts:=ordinary_root_first_cleanup_counts_from_profile P Q F H π d X T Z W r η ell t K ht
    pR pH p density tR tH L βe₀ βh₀ βe βh s j raw σ hr profile hmE hmH hevent hhevent
  have hinner:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤ν:=by
    intro w
    have hd:((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤
        ((ordinaryPhysicalGraph R S).degree w:ℝ):=by
      exact_mod_cast SimpleGraph.degree_le_of_le (show spanningRestriction (ordinaryPhysicalGraph R S)
        (ordinaryInnerVertices X Z)≤ordinaryPhysicalGraph R S from by intro a b hab;exact ((spanningRestriction_adj _ _ _ _).mp hab).1)
    exact hd.trans (O.cleanup.degree w)
  intro u hu a ha c hc
  have hsurvive:=ordinary_inner_extensions_after_local_cover Q₁ R H₁ S X Z ν hinner u hu a c ha hc
  have hpre:(p^3*βe/2)*Fintype.card (V⊕U)≤
      (((X.filter (fun v=>H₁ v u))∩Q₁.neighborFinset a∩Q₁.neighborFinset c).card:ℝ):=by
    convert hcounts.1 u a c using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  have hsurvive':(((X.filter (fun v=>H₁ v u))∩Q₁.neighborFinset a∩Q₁.neighborFinset c).card:ℝ)-3*ν≤
      (((X.filter (fun v=>H₂ v u))∩Q₂.neighborFinset a∩Q₂.neighborFinset c).card:ℝ):=by
    convert hsurvive using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  linarith only [hpre,hsurvive']
end Oberwolfach
