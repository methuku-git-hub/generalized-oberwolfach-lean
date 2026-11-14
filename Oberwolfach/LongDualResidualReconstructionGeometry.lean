module

public import Oberwolfach.LongDualResidualPhysicalInjective
public import Oberwolfach.LongPartitionedResidualDivisible
public import Oberwolfach.MarkedPhysicalHostContainment

@[expose] public section
/-! The actual oriented residual has the physical-edge properties needed
for factor reconstruction, and avoids the complement's small graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite

theorem long_dual_residual_reconstruction_geometry
    {V:Type} [Fintype V] [LinearOrder V] [Nonempty V]
    (S Small:SimpleGraph V) (M:V→V→ℕ)
    (hphysical:∀x y,M x y+M y x=if S.Adj x y then 1 else 0)
    (π:Equiv.Perm V) (T:Finset {a:V×V // longEligibleResidualArc M Small ⊥ a}):
    let P:=longEligibleResidualArc M Small ⊥
    let E:=residualOrdinaryArc P T
    let K:=residualMarkedArc P T
    let tail:=fun e:E=>e.val.val.1
    let head:=fun e:E=>e.val.val.2
    let ktail:=fun e:K=>e.val.val.1
    let khead:=fun e:K=>π.symm e.val.val.2
    let Rrim:=markedPhysicalRimSet tail head ktail khead π;
    (∀e:E,tail e≠head e) ∧ (∀e:K,ktail e≠π (khead e)) ∧
    Function.Injective (markedPhysicalEdge tail head ktail khead π) ∧
    physicalEdgeGraph Rrim≤S ∧
    (∀x y,Small.Adj x y→({x,y}:Finset V)∉Rrim) :=by
  intro P E K tail head ktail khead Rrim
  have hgraph:∀e:{a:V×V // P a},(S\Small).Adj e.val.1 e.val.2:=by
    intro e
    have hp:=hphysical e.val.1 e.val.2
    have hm:=e.property.1
    have hs:S.Adj e.val.1 e.val.2:=by
      split_ifs at hp with hh
      · exact hh
      · omega
    exact ⟨hs,e.property.2.1⟩
  have hloops:=long_dual_residual_physical_injective S Small M hphysical π T
  have hRim:physicalEdgeGraph Rrim≤S\Small:=by
    apply marked_physical_host_graph_le (S\Small) tail head ktail khead π
    · intro e;exact hgraph e.val
    · intro e;simpa only [ktail,khead,Equiv.apply_symm_apply] using hgraph e.val
  refine ⟨hloops.1,hloops.2.1,hloops.2.2,?_,?_⟩
  · intro x y hxy;exact (hRim hxy).1
  · intro x y hxy hrim
    exact (hRim ⟨hxy.ne,hrim⟩).2 hxy
end Oberwolfach
