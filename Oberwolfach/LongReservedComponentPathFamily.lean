module

public import Oberwolfach.LongReservedComponentBlocks

@[expose] public section
/-! Any injected assignment of requests to complete blocks in a component
produces disjoint extended paths of the requested lengths. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_reserved_component_path_family
    {V J:Type*} [Fintype V] [DecidableEq V] [Fintype J]
    (G:SimpleGraph V) (hG:G.IsRegularOfDegree 2)
    (C:G.ConnectedComponent) [Fintype C] (c d:ℕ)
    (index:J↪Fin (Fintype.card C/(c*d+5))) (t:J→ℕ) (ht:∀a,t a≤d):
    ∃f:∀a:J,Fin (c*t a+5)↪C,
      (∀(a:J) (j:Fin (c*t a+4)),C.toSimpleGraph.Adj
        (f a ⟨j.val,by omega⟩) (f a ⟨j.val+1,by omega⟩)) ∧
      (∀a b:J,a≠b→Disjoint (Finset.univ.image (f a)) (Finset.univ.image (f b))) := by
  obtain ⟨hthree,⟨e⟩⟩:=component_regular_two_cycle_iso G hG C
  have hfit (a:J):(c*d+5)*((index a).val+1)≤Fintype.card C:=by
    have hpos:0<c*d+5:=by omega
    have hh:(index a).val+1≤Fintype.card C/(c*d+5):=by have ha:=(index a).isLt;omega
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hpos).mp hh
  let f:=fun a:J=>longReservedComponentBlock G C e c d (t a) (index a).val (ht a) (hfit a)
  refine ⟨f,?_,?_⟩
  · intro a j
    exact long_reserved_component_block_edges G C e hthree c d (t a) (index a).val (ht a) (hfit a) j
  · intro a b hab
    have hij:(index a).val≠(index b).val:=by
      intro heq
      apply hab
      apply index.injective
      exact Fin.ext heq
    exact long_reserved_component_blocks_disjoint G C e c d (t a) (t b) (index a).val (index b).val (ht a) (ht b) (hfit a) (hfit b) hij
end Oberwolfach
