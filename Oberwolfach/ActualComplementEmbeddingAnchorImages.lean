module

public import Oberwolfach.ActualComplementEmbeddingGlue
public import Oberwolfach.ActualComplementEmbeddingReserved
public import Oberwolfach.SelectedAnchorsRestrictedAvoidance

@[expose] public section
/-! Construct the complement embedding and preserve reserved labels outside
the final paths without embedding their interiors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_complement_embedding_preserves_reserved_labels_from_anchor_images
    {X V I K J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [Nonempty V] [Fintype I]
    [DecidableEq K] [DecidableEq J] {F:SimpleGraph X}
    (data:ActualResidualData (K:=K) (J:=J) F) (hF:F.IsRegularOfDegree 2)
    (hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)
    (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X)
    (hDR:Disjoint (bufferedPathStrictInterior n inner) data.remaining)
    (ψ:X→V) (hψ:Set.InjOn ψ (↑(data.oldDomain\bufferedPathStrictInterior n inner):Set X))
    (B:Finset {x // x∈data.remaining})
    (g Φ:{x // x∈data.remaining}→V) (L C Z Y:Finset V)
    (hA₀B:residualSubtypeSet data.remaining data.prescribed⊆B)
    (hΦ:Function.Injective Φ)
    (hg:∀x∈residualSubtypeSet data.remaining data.prescribed,g x=ψ x.val)
    (hΦg:∀x∈B,Φ x=g x)
    (himage:B.image g=(residualSubtypeSet data.remaining data.prescribed).image (fun x=>ψ x.val)∪C∪Z)
    (hOldC:Disjoint ((data.oldDomain\bufferedPathStrictInterior n inner).image ψ) C)
    (hOldZ:Disjoint ((data.oldDomain\bufferedPathStrictInterior n inner).image ψ) Z)
    (hfree:∀x,x∉B→Φ x∈L) (hL:Disjoint L ((data.oldDomain\bufferedPathStrictInterior n inner).image ψ))
    (hOldAvoid:∀x,x∈data.oldDomain→x∉bufferedPathFullDomain n inner→ψ x∉Y)
    (hCY:Disjoint C Y) (hZY:Disjoint Z Y) (hListAvoid:Disjoint L Y):
    ∃fC:{x // x∉bufferedPathStrictInterior n inner}↪V,
      (∀x:{x // x∉bufferedPathStrictInterior n inner},x.val∈data.oldDomain→fC x=ψ x.val) ∧
      (∀x:{x // x∈data.remaining},∀hx:x.val∉bufferedPathStrictInterior n inner,fC ⟨x.val,hx⟩=Φ x) ∧
      Disjoint (outsideBufferedPathImage n inner fC) Y:=by
  have hAnchorAvoid:∀x∈B,x.val∉bufferedPathFullDomain n inner → g x∉Y:=by
    apply selected_anchors_avoid_reserved_outside (residualSubtypeSet data.remaining data.prescribed) B
      (fun x=>ψ x.val) g Φ C Z Y (fun x=>x.val∉bufferedPathFullDomain n inner)
      hA₀B hΦ hg hΦg himage ?_ hCY hZY
    intro x hx hxout
    have hpres:x.val∈data.prescribed:=by
      simpa only [residualSubtypeSet,Finset.mem_filter,Finset.mem_univ,true_and] using hx
    have hold:x.val∈data.oldDomain:=
      Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hpres))
    exact hOldAvoid x.val hold hxout
  exact actual_complement_embedding_preserves_reserved_labels data hF hCycle n inner hDR ψ hψ B g Φ L C Z Y
    hA₀B hΦ hg hΦg himage hOldC hOldZ hfree hL hOldAvoid hAnchorAvoid hListAvoid
end Oberwolfach
