module

public import Oberwolfach.OrdinaryRootFirstCleanupOutcome
public import Oberwolfach.OrdinaryDeepRootFreeFamilies

@[expose] public section
/-! Certificate for the final boundary finish on the actual host left by
the root cover, approximate packing and cleanup. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryRootFirstCleanRemainderRim
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t ν:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W r η ell) (σ:Sym2 (V⊕U)→Bool)
    (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W r η ell t ν D σ):SimpleGraph V:=
  ((Q\O.context.cover.rim)\ordinaryRootFirstPackingRim Q F H X T Z W r η ell t O.context)\wheelFamilyRim O.cleanup.wheels

def ordinaryRootFirstCleanRemainderSpokes
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t ν:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W r η ell) (σ:Sym2 (V⊕U)→Bool)
    (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W r η ell t ν D σ):V→U→Prop:=
  fun v u=>((H v u∧¬O.context.cover.spokes v u)∧
    ¬ordinaryRootFirstPackingSpokes Q F H X T Z W r η ell t O.context v u)∧¬wheelFamilySpokes O.cleanup.wheels v u

structure OrdinaryRootFirstFinishData
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t ν:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W r η ell) (σ:Sym2 (V⊕U)→Bool)
    (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W r η ell t ν D σ) (limit:ℝ) where
  rim:SimpleGraph V
  spokes:V→U→Prop
  rim_sub:rim≤ordinaryRootFirstCleanRemainderRim Q F H X T Z W r η ell t ν D σ O
  spoke_sub:∀v u,spokes v u → ordinaryRootFirstCleanRemainderSpokes Q F H X T Z W r η ell t ν D σ O v u
  host_decomposition:HasResourceDecomposition
    (ordinaryWheelResources (P:=ordinaryRootFirstCleanRemainderRim Q F H X T Z W r η ell t ν D σ O)
      (F:=F) (Hbase:=ordinaryRootFirstCleanRemainderSpokes Q F H X T Z W r η ell t ν D σ O) (r:=r))
    (ordinaryHostResources rim spokes)
  decomposition:HasOrdinaryWheelDecomposition rim spokes r
  rim_inside:(ordinaryRootFirstCleanRemainderRim Q F H X T Z W r η ell t ν D σ O\rim).support⊆(X:Set V)
  spoke_inside:∀v u,ordinaryRootFirstCleanRemainderSpokes Q F H X T Z W r η ell t ν D σ O v u∧¬spokes v u→v∈X∧u∈Z
  inner_degree:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph rim spokes) (ordinaryInnerVertices X Z)).degree w:ℝ)≤limit
  avoids_star:Disjoint (ordinaryPhysicalGraph rim spokes) (ordinaryDeepRootStar T W)
end Oberwolfach
