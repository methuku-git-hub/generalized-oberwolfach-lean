module

public import Oberwolfach.OrdinaryHostDecompositions
public import Oberwolfach.OrdinaryExactDecomposition

@[expose] public section
/-! Glue a wheel packing outside an absorber and its leftover to an exact
absorbing decomposition, retaining the same physical resource set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_absorbed_remainder_completion {V U:Type} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    (P F Q:SimpleGraph V) (Hbase H:V→U→Prop) (r:ℕ)
    (A T:Finset (Sym2 V⊕(V×U)))
    (hA:A⊆ordinaryHostResources Q H) (hT:T⊆ordinaryHostResources Q H)
    (hpack:HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r))
      (ordinaryHostResources Q H\(A∪T)))
    (habs:HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r)) (A∪T)):
    HasOrdinaryWheelDecomposition Q H r :=by
  let R:=ordinaryHostResources Q H
  have hsub:A∪T⊆R:=Finset.union_subset hA hT
  have hdis:Disjoint (R\(A∪T)) (A∪T):=by
    apply Finset.disjoint_left.mpr
    intro e he he'
    exact (Finset.mem_sdiff.mp he).2 he'
  have hh:=resource_decomposition_union
    (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r)) (R\(A∪T)) (A∪T) hpack habs hdis
  have heq:(R\(A∪T))∪(A∪T)=R:=Finset.sdiff_union_of_subset hsub
  rw [heq] at hh
  exact ordinary_host_decomposition_forget R hh
end Oberwolfach
