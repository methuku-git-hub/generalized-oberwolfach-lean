module

public import Oberwolfach.LongReservedBlockAllocation
public import Oberwolfach.LongReservedSigmaBlocks

@[expose] public section
/-! The prescribed requests can be placed in distinct blocks of the
specified cycles, producing actual disjoint extended paths in the factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_reserved_actual_factor_paths
    {V I J:Type*} [Fintype V] [DecidableEq V] [Fintype I] [Fintype J]
    (G:SimpleGraph V) (hG:G.IsRegularOfDegree 2)
    (components:I↪G.ConnectedComponent) (c d:ℕ) (t:J→ℕ) (ht:∀a,t a≤d)
    (hcapacity:Fintype.card J≤∑i:I,Fintype.card (components i)/(c*d+5)):
    ∃index:J↪LongReservedBlockIndex G components c d,
    ∃f:∀a:J,Fin (c*t a+5)↪V,
      (∀(a:J) (j:Fin (c*t a+4)),G.Adj
        (f a ⟨j.val,by omega⟩) (f a ⟨j.val+1,by omega⟩)) ∧
      (∀a j,f a j ∈ (components (index a).1).supp) ∧
      (∀a b:J,a≠b→Disjoint (Finset.univ.image (f a)) (Finset.univ.image (f b))) := by
  obtain ⟨index⟩:=long_reserved_requests_fit_blocks (fun i:I=>Fintype.card (components i)/(c*d+5)) hcapacity
  let e:∀i:I,SimpleGraph.cycleGraph (Fintype.card (components i)) ≃g (components i).toSimpleGraph:=
    fun i=>Classical.choice (component_regular_two_cycle_iso G hG (components i)).2
  have hthree (i:I):3≤Fintype.card (components i):=(component_regular_two_cycle_iso G hG (components i)).1
  let f:∀a:J,Fin (c*t a+5)↪V:=fun a=>longReservedSigmaBlock G components c d e (index a) (t a) (ht a)
  refine ⟨index,f,?_,?_,?_⟩
  · intro a j
    exact long_reserved_sigma_block_edges G components c d e hthree (index a) (t a) (ht a) j
  · intro a j
    exact (longReservedComponentBlock G (components (index a).1) (e (index a).1) c d (t a) (index a).2.val (ht a)
      (long_reserved_sigma_block_fit G components c d (index a)) j).property
  · intro a b hab
    apply long_reserved_sigma_blocks_disjoint G components c d e (index a) (index b) (t a) (t b) (ht a) (ht b)
    intro heq
    exact hab (index.injective heq)
end Oberwolfach
