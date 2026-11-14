module

public import Oberwolfach.TriangleTransformerUniformBounds
public import Oberwolfach.OrdinaryBalancedRootCounts

@[expose] public section
/-! Bound the edge and incidence complexities of a balanced root graph
from its bounded row and hub vertex sets. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

 theorem triangle_root_spokes_bounded {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (H:V→U→Prop) (R:Finset V) (B:Finset U)
    (h:∀ v u,H v u→v∈R∧u∈B):
    Fintype.card {e:V×U // H e.1 e.2}≤R.card*B.card:=by
  let f:{e:V×U // H e.1 e.2}→{v:V // v∈R}×{u:U // u∈B}:=fun e=>
    (⟨e.val.1,(h e.val.1 e.val.2 e.property).1⟩,⟨e.val.2,(h e.val.1 e.val.2 e.property).2⟩)
  have hf:Function.Injective f:=by
    intro a b hab
    apply Subtype.ext
    exact Prod.ext (congrArg (fun z:({v:V // v∈R}×{u:U // u∈B})=>z.1.val) hab)
      (congrArg (fun z:({v:V // v∈R}×{u:U // u∈B})=>z.2.val) hab)
  have hh:=Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_prod,Fintype.card_coe] using hh

 theorem triangle_root_complexity_bound {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (G:SimpleGraph V) (H:V→U→Prop) (R₀:Finset V) (B₀:Finset U) (q:ℕ)
    (hbalance:∀ v,G.degree v=2*((Finset.univ:Finset U).filter (H v)).card)
    (hsupport:∀ v u,H v u→v∈R₀∧u∈B₀) (hR:R₀.card≤q) (hB:B₀.card≤q):
    G.edgeFinset.card≤q*q ∧ Fintype.card {e:V×U // H e.1 e.2}≤q*q ∧
    Fintype.card (Σ v,G.neighborSet v)≤2*(q*q):=by
  have ht:Fintype.card {e:V×U // H e.1 e.2}≤q*q:=
    (triangle_root_spokes_bounded H R₀ B₀ hsupport).trans (Nat.mul_le_mul hR hB)
  have hq:∀ u,((Finset.univ:Finset V).filter (fun v=>H v u)).card≤R₀.card:=by
    intro u
    apply Finset.card_le_card
    intro v hv
    exact (hsupport v u (Finset.mem_filter.mp hv).2).1
  have hn:Fintype.card {u:U // ∃v,H v u}≤Fintype.card U:=Fintype.card_subtype_le _
  obtain ⟨he,hd,_⟩:=balanced_root_edge_counts G H hbalance R₀.card (Fintype.card U) hq hn
  exact ⟨he.le.trans ht,ht,by rw [hd,he];exact Nat.mul_le_mul_left 2 ht⟩
end Oberwolfach
