module

public import Oberwolfach.LongReservedActualFactorPaths

@[expose] public section
/-! The long source blocks and matched short components avoid all reserved
components: their sizes are above the cutoff, or they were assigned outside
the reserved component set, respectively. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_source_pieces_avoid_reserved
    {n K:ℕ} {T A:Type} [Fintype T] [Fintype A]
    (F:SimpleGraph (Fin n)) (i₀:Fin K) (Cres:Finset F.ConnectedComponent)
    (hCres:∀C,C∈Cres→Fintype.card C=i₀.val+1)
    (assign:A↪↥(Finset.univ\Cres))
    (c d:ℕ)
    (E:∀C:F.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph):
    let I:={C:F.ConnectedComponent // K<Fintype.card C}
    let components:I↪F.ConnectedComponent:=Function.Embedding.subtype _;
    ∀(block:T↪LongReservedBlockIndex F components c d),
      (∀i (k:Fin (c*d+5)),F.connectedComponentMk
        (longReservedSigmaBlock F components c d (fun j=>E (components j)) (block i) d le_rfl k)∉Cres) ∧
      (∀a x,x∈(assign a).val.supp→F.connectedComponentMk x∉Cres) :=by
  intro I components block
  constructor
  · intro i k hres
    have hmem:(longReservedSigmaBlock F components c d (fun j=>E (components j)) (block i) d le_rfl k)∈
        (components (block i).1).supp:=
      (longReservedComponentBlock F (components (block i).1) (E (components (block i).1)) c d d (block i).2.val le_rfl
        (long_reserved_sigma_block_fit F components c d (block i)) k).property
    have heq:F.connectedComponentMk
        (longReservedSigmaBlock F components c d (fun j=>E (components j)) (block i) d le_rfl k)=components (block i).1:=
      (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hmem
    rw [heq] at hres
    have hlarge:K<Fintype.card (components (block i).1):=(block i).1.property
    have hsmall:=hCres (components (block i).1) hres
    have hi:=i₀.isLt
    omega
  · intro a x hx
    rw [(SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hx]
    exact (Finset.mem_sdiff.mp (assign a).property).2
end Oberwolfach
