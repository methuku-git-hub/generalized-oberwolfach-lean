module

public import Oberwolfach.TriangleFactorHubTrade

@[expose] public section
/-! A wheel decomposition supported on a conflict-free vertex set remains a
decomposition in the host with the conflict condition imposed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem wheel_decomposition_conflict_recovery {V U:Type} [Fintype V] [DecidableEq V]
    [Fintype U] [DecidableEq U] (Q F R:SimpleGraph V) (H S:V→U→Prop) (T:Finset V) (r:ℕ)
    (hR:R≤Q) (hS:∀ v u,S v u→H v u)
    (hsupp:∀ v w,R.Adj v w→v∈T∧w∈T) (hfree:∀ v∈T,∀ w∈T,¬F.Adj v w)
    (hdec:HasOrdinaryWheelDecomposition R S r):
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
      (ordinaryHostResources R S):=by
  obtain ⟨M,hM,hcover⟩:=hdec
  apply ordinary_decomposition_recover_host Q F H (ordinaryHostResources R S)
    (ordinary_host_resources_monotone R Q S H hR hS) M ⟨hM,hcover⟩
  intro W hW v hv w hw
  have hsub:ordinaryWheelResources W⊆ordinaryHostResources R S:=by
    intro e he
    rw [←hcover]
    exact Finset.mem_biUnion.mpr ⟨W,hW,he⟩
  have hrim:(ordinaryWheelRim W)≤R:=((ordinaryWheelResources_subset_host W R S).mp hsub).1
  have hvR:v∈R.support:=SimpleGraph.support_mono hrim hv
  have hwR:w∈R.support:=SimpleGraph.support_mono hrim hw
  obtain ⟨v',hv'⟩:=R.mem_support.mp hvR
  obtain ⟨w',hw'⟩:=R.mem_support.mp hwR
  exact hfree v (hsupp v v' hv').1 w (hsupp w w' hw').1
end Oberwolfach
