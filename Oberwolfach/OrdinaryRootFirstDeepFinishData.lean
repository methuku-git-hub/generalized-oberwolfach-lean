module

public import Oberwolfach.OrdinaryRootFirstFinishData
public import Oberwolfach.OrdinaryDeepBlocker

@[expose] public section
/-! A triangle boundary finish need only avoid the deeper protected block;
its deeper-boundary cost is accounted for in the level budget. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

structure OrdinaryRootFirstDeepFinishData
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
  avoids_deep:Disjoint (ordinaryPhysicalGraph rim spokes) (ordinaryDeepBlocker T W)
end Oberwolfach
