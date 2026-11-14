module

public import Oberwolfach.OrdinaryFixedTargetToColumnInputs

@[expose] public section

/-! The column refinement preserves the already selected reservoir and is
uniform over every target allowed by the caller. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_uniform_reservoir_target_columns_eventually
    (θ δ a γ:ℝ) (hθ:0≤θ) (hδ:0<δ) (hθδ:θ≤δ/8):
    ∃N:ℕ,∀{n K:ℕ},N≤n→∀{U:Type} [Fintype U] [DecidableEq U],Fintype.card U≤n→
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Cres:∀u,Finset (F u).ConnectedComponent) (i₀:Fin K) (rsv lam:ℝ)
    (m d:ℕ) (π:Equiv.Perm (Fin n)) (P:SimpleGraph (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (Inner:Finset (Fin n)) (Hubs:Finset U) (lamList bRate z:ℝ) (q s:U→Bool→ℝ)
    (Allowed:SimpleGraph (Fin n)→Prop)
    (Witness:Finset (Sym2 (Fin n)⊕(Fin n×U))→SimpleGraph (Fin n)→(Fin n→U→Prop)→Prop),
    OrdinaryZeroRetentionEvent π d false σ→
    (∀w,1-(∑g,q w g)-(∑j,s w j)≤2*θ)→
    (∀v∈Inner,|rawIntervalUnassignedColumnCount π d (fun e=>σ (Sum.inr e)) v Hubs-
      ∑w∈Hubs,(1-(∑g,q w g)-(∑j,s w j))|<(Inner.card:ℝ)^(3/4:ℝ))→
    2*((max a γ)*n)≤δ*n/8→
    (∃Kabs JQ JH,Witness Kabs JQ JH ∧ ∀Target,Allowed Target→
      OrdinaryFixedPostmatchingTargetInputs F hF Cres i₀ rsv θ lam a γ m d π P Target σ Inner Hubs Kabs lamList bRate z)→
    ∃Kabs JQ JH,Witness Kabs JQ JH ∧ ∀Target,Allowed Target→
      OrdinaryFixedPostmatchingColumnInputs F hF Cres i₀ rsv θ lam a γ m d π P Target σ Inner Hubs Kabs lamList bRate z δ :=by
  obtain ⟨N,hcol⟩:=ordinary_fixed_target_to_column_inputs_eventually θ δ a γ hθ hδ hθδ
  refine ⟨N,?_⟩
  intro n K hn U _ _ hU F hF Cres i₀ rsv lam m d π P σ Inner Hubs lamList bRate z q s Allowed Witness
    hzero hslack hlocal hmatching hbase
  obtain ⟨Kabs,JQ,JH,hW,hbase⟩:=hbase
  refine ⟨Kabs,JQ,JH,hW,?_⟩
  intro Target hTarget
  exact hcol hn hU F hF Cres i₀ rsv lam m d π P Target σ Inner Hubs Kabs lamList bRate z q s
    hzero hslack hlocal hmatching (hbase Target hTarget)
end Oberwolfach
