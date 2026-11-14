module

public import Oberwolfach.OrdinaryFixedPostmatchingTargetInputs
public import Oberwolfach.OrdinaryFixedPostmatchingColumnInputs
public import Oberwolfach.OrdinarySelectedPostDemandTargetColumns

@[expose] public section

/-! Refine the same target-input witness with its actual target-column load. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fixed_target_to_column_inputs_eventually
    (θ δ a γ:ℝ) (hθ:0≤θ) (hδ:0<δ) (hθδ:θ≤δ/8):
    ∃N:ℕ,∀{n K:ℕ},N≤n→∀{U:Type} [Fintype U] [DecidableEq U],Fintype.card U≤n→
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Cres:∀u,Finset (F u).ConnectedComponent) (i₀:Fin K) (rsv lam:ℝ)
    (m d:ℕ) (π:Equiv.Perm (Fin n)) (P Target:SimpleGraph (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (Inner:Finset (Fin n)) (Hubs:Finset U) (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×U)))
    (lamList bRate z:ℝ) (q s:U→Bool→ℝ),
    OrdinaryZeroRetentionEvent π d false σ→
    (∀w,1-(∑g,q w g)-(∑j,s w j)≤2*θ)→
    (∀v∈Inner,|rawIntervalUnassignedColumnCount π d (fun e=>σ (Sum.inr e)) v Hubs-
      ∑w∈Hubs,(1-(∑g,q w g)-(∑j,s w j))|<(Inner.card:ℝ)^(3/4:ℝ))→
    2*((max a γ)*n)≤δ*n/8→
    OrdinaryFixedPostmatchingTargetInputs F hF Cres i₀ rsv θ lam a γ m d π P Target σ Inner Hubs Kabs lamList bRate z→
    OrdinaryFixedPostmatchingColumnInputs F hF Cres i₀ rsv θ lam a γ m d π P Target σ Inner Hubs Kabs lamList bRate z δ :=by
  obtain ⟨N,hcol⟩:=ordinary_selected_post_demand_target_columns_eventually θ δ a γ hθ hδ hθδ
  refine ⟨N,?_⟩
  intro n K hn U _ _ hU F hF Cres i₀ rsv lam m d π P Target σ Inner Hubs Kabs lamList bRate z q s
    hzero hslack hlocal hmatching hbase
  unfold OrdinaryFixedPostmatchingTargetInputs at hbase
  unfold OrdinaryFixedPostmatchingColumnInputs
  obtain ⟨h1,h2,h3,h4,h5,h6,htarget⟩:=hbase
  refine ⟨h1,h2,h3,h4,h5,h6,?_⟩
  exact hcol hn hU F hF Cres i₀ rsv lam m d π P _ Target _ _ Inner Hubs bRate z σ 0 _ q s
    hzero hslack hlocal hmatching htarget
end Oberwolfach
