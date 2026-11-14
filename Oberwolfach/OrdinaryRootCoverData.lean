module

public import Oberwolfach.OrdinaryDeepBlockerNested
public import Oberwolfach.OrdinaryWheelRemainders

@[expose] public section
/-! A root cover records the actual wheels' resources, their local degree
costs, their root coverage and their avoidance of the deeper induced pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

structure OrdinaryRootCoverData (Q F:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell:ℝ) where
  rim:SimpleGraph V
  spokes:V→U→Prop
  rim_sub:rim≤Q
  spoke_sub:∀v u,spokes v u→H v u
  host_decomposition:HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
    (ordinaryHostResources rim spokes)
  decomposition:HasOrdinaryWheelDecomposition rim spokes r
  inner_degree:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph rim spokes) (ordinaryInnerVertices X Z)).degree w:ℝ)≤η
  outside_degree:∀w∉ordinaryInnerVertices X Z,((ordinaryPhysicalGraph rim spokes).degree w:ℝ)≤ell
  avoids_deep:Disjoint (ordinaryPhysicalGraph rim spokes) (ordinaryDeepBlocker T W)
  covers_rim:∀v∈T,∀w∉X,Q.Adj v w → rim.Adj v w
  covers_row:∀v∈T,∀u∉Z,H v u→spokes v u
  covers_column:∀u∈W,∀v∉X,H v u→spokes v u
end Oberwolfach
