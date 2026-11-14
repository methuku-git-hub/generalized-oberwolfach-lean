module

public import Oberwolfach.OrdinaryRootFirstCleanupGivenCounts

@[expose] public section
/-! Named physical graphs and data for the cleanup following a lifted
root-first packing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryRootFirstPackingRim
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t:ℝ)
    (K:OrdinaryRootFirstPackingContext Q F H X T Z W r η ell t):SimpleGraph V:=
  (ordinaryWheelRimGraph K.packing.wheels).map (⟨Subtype.val,Subtype.val_injective⟩:↥(Finset.univ\T)↪V)

def ordinaryRootFirstPackingSpokes
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t:ℝ)
    (K:OrdinaryRootFirstPackingContext Q F H X T Z W r η ell t):V→U→Prop:=
  ordinaryMappedSpokes (ordinaryPackingSpokes K.packing.wheels)
    (⟨Subtype.val,Subtype.val_injective⟩:↥(Finset.univ\T)↪V)
    (⟨Subtype.val,Subtype.val_injective⟩:↥(Finset.univ\W)↪U)

structure OrdinaryRootFirstCleanupOutcome
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t ν:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W r η ell) (σ:Sym2 (V⊕U)→Bool) where
  context:OrdinaryRootFirstPackingContext Q F H X T Z W r η ell t
  cover_eq:context.cover=D
  reserve_eq:context.reserve=retainedGraph (ordinaryBoundaryGraph (Q\D.rim)
    (fun v u=>H v u∧¬D.spokes v u) X Z) σ
  cleanup:
    let R:=ordinaryRootFirstPackingRim Q F H X T Z W r η ell t context
    let S:=ordinaryRootFirstPackingSpokes Q F H X T Z W r η ell t context
    OrdinaryOutsideCleanupData ((Q\context.cover.rim)\R) F
      (fun v u=>(H v u∧¬context.cover.spokes v u)∧¬S v u) X Z
      (ordinaryPhysicalGraph R S) r ν
  avoids_deep:
    Disjoint (ordinaryPhysicalGraph (wheelFamilyRim cleanup.wheels) (wheelFamilySpokes cleanup.wheels))
      (ordinaryDeepBlocker T W)
end Oberwolfach
