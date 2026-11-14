module

public import Oberwolfach.OrdinaryCleanupCountsAfterPacking
public import Oberwolfach.OrdinaryPackingCleanupData
public import Oberwolfach.OrdinaryPhysicalCleanupEdit
public import Oberwolfach.OrdinaryBoundaryCountsAfterPhysicalEdit

@[expose] public section
/-! The extension counts needed to finish endpoint pairings survive the
    actual approximate packing and its sparse cleanup on the same samples. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_boundary_counts_after_sampled_cleanup
    (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d r:ℕ)
    (X:Finset V) (Z:Finset U) (pR pH p density tR tH L βe βh t tCleanup:ℝ)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color) (σ:Sym2 (V⊕U)→Bool)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH L βe βh s j raw)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card)
    (hevent:OrdinaryBoundaryExtensionGood Q H X βe p σ)
    (hhevent:OrdinaryBoundaryHubPairGood H Z βh p σ)
    (M:OrdinaryUnreservedPackingData Q F H X Z (retainedGraph (ordinaryBoundaryGraph Q H X Z) σ) r t):
    let R:=retainedGraph (ordinaryBoundaryGraph Q H X Z) σ;
    let Qpost:=ordinaryPackingPostRim Q F H X Z R r t M;
    let Hpost:=ordinaryPackingPostSpokes Q F H X Z R r t M;
    let C:=ordinaryPackingUsedGraph Q F H X Z R r t M;
    ∀(cleanup:OrdinaryOutsideCleanupData Qpost F Hpost X Z C r tCleanup),
    let Qfinal:=Qpost\wheelFamilyRim cleanup.wheels;
    let Hfinal:=fun v u=>Hpost v u∧¬wheelFamilySpokes cleanup.wheels v u;
    ∀u a c,(p^3*βe/2)*Fintype.card (V⊕U)-3*tCleanup≤
      (((X.filter (fun v=>Hfinal v u))∩Qfinal.neighborFinset a∩Qfinal.neighborFinset c).card:ℝ):=by
  intro R Qpost Hpost C cleanup Qfinal Hfinal
  have hfacts:=ordinary_packing_post_facts Q F H X Z R r t M hbal hdiv
  have hcounts:=ordinary_cleanup_counts_after_packing P Q F H π d r X Z pR pH p density tR tH L βe βh t
    s j raw σ profile hevent hhevent M hfacts
  have hedit:=ordinary_physical_cleanup_edit Qpost (wheelFamilyRim cleanup.wheels) Hpost
    (wheelFamilySpokes cleanup.wheels) tCleanup cleanup.degree
  have hfinal:=ordinary_boundary_counts_after_physical_edit Qpost Qfinal Hpost Hfinal X
    ((p^3*βe/2)*Fintype.card (V⊕U)) tCleanup hcounts.1 hedit
  intro u a c
  convert hfinal u a c using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
