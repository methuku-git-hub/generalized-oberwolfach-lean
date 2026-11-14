module

public import Oberwolfach.OrdinaryBoundaryParentCommon

@[expose] public section
/-! Common neighborhoods in an induced domain have exactly the same
cardinality as their images in the ambient graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem ordinary_induced_common_card
    (Q:SimpleGraph V) (A:Finset V) (S:Finset {v:V // v∈A}):
    (common Finset.univ S (fun x=>(Q.induce (A:Set V)).neighborFinset x)).card=
      (common A (S.image Subtype.val) (fun x=>Q.neighborFinset x)).card:=by
  let M:=common Finset.univ S (fun x=>(Q.induce (A:Set V)).neighborFinset x)
  let N:=common A (S.image Subtype.val) (fun x=>Q.neighborFinset x)
  have himage:M.image Subtype.val=N:=by
    ext v
    constructor
    · intro hv
      obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hv
      simp only [M,mem_common_iff] at hx
      simp only [N,mem_common_iff]
      refine ⟨x.property,?_⟩
      intro y hy
      obtain ⟨y',hy',rfl⟩:=Finset.mem_image.mp hy
      have hh:=hx.2 y' hy'
      simpa only [SimpleGraph.mem_neighborFinset,SimpleGraph.induce_adj] using hh
    · intro hv
      simp only [N,mem_common_iff] at hv
      let x:{v:V // v∈A}:=⟨v,hv.1⟩
      apply Finset.mem_image.mpr
      refine ⟨x,?_,rfl⟩
      simp only [M,mem_common_iff]
      refine ⟨Finset.mem_univ _,?_⟩
      intro y hy
      have hh:=hv.2 y.val (Finset.mem_image.mpr ⟨y,hy,rfl⟩)
      simpa only [SimpleGraph.mem_neighborFinset,SimpleGraph.induce_adj] using hh
  have hc:=Finset.card_image_of_injective M (Subtype.val_injective : Function.Injective (Subtype.val : {v:V // v∈A}→V))
  change M.card=N.card
  calc
    M.card=(M.image Subtype.val).card:=hc.symm
    _=N.card:=congrArg Finset.card himage
end Oberwolfach
