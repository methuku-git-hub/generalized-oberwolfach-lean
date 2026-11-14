module

public import Oberwolfach.OrdinaryUnreservedRootFreeDomain
public import Oberwolfach.OrdinaryInducedUnreservedPair

@[expose] public section
/-! After the actual root cover, the unreserved pair on the induced
nonroot domains maps exactly onto the ambient unreserved pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_free_unreserved_map
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell:ℝ)
    (hTX:T⊆X) (hWZ:W⊆Z) (D:OrdinaryRootCoverData Q F H X T Z W r η ell)
    (R:SimpleGraph (V⊕U)):
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    let φ:A↪V:=⟨Subtype.val,Subtype.val_injective⟩;
    let ψ:B↪U:=⟨Subtype.val,Subtype.val_injective⟩;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X);
    let Zf:Finset B:=Finset.univ.filter (fun u=>u.val∈Z);
    let Rf:=R.comap (φ.sumMap ψ);
    let Q':=Q\D.rim;let H':=fun v u=>H v u∧¬D.spokes v u;
    (ordinaryUnreservedRim (Q'.induce (A:Set V)) Xf Rf).map φ=ordinaryUnreservedRim Q' X R ∧
    ordinaryMappedSpokes (ordinaryUnreservedSpokes (fun (v:A) (u:B)=>H' v.val u.val) Xf Zf Rf) φ ψ=
      ordinaryUnreservedSpokes H' X Z R:=by
  intro A B φ ψ Xf Zf Rf Q' H'
  let QR:=ordinaryUnreservedRim Q' X R
  let HS:=ordinaryUnreservedSpokes H' X Z R
  have hg:=ordinary_unreserved_root_free_domain Q F H X T Z W r η ell hTX hWZ D R
  have hr:QR=spanningRestriction QR A:=by
    ext x y
    have hh:=congrArg (fun G:SimpleGraph (V⊕U)=>G.Adj (Sum.inl x) (Sum.inl y)) hg
    apply Iff.of_eq
    simpa only [ordinaryPhysicalGraph,spanningRestriction_adj,ordinaryInnerVertices_left] using hh
  have hs:HS=(fun v u=>HS v u∧v∈A∧u∈B):=by
    funext v u
    apply propext
    have hh:=congrArg (fun G:SimpleGraph (V⊕U)=>G.Adj (Sum.inl v) (Sum.inr u)) hg
    apply Iff.of_eq
    simpa only [ordinaryPhysicalGraph,spanningRestriction_adj,ordinaryInnerVertices_left,ordinaryInnerVertices_right] using hh
  have hp:=ordinary_induced_unreserved_pair Q' H' X T Z W R
  constructor
  · rw [hp.1,ordinary_induced_rim_map]
    exact hr.symm
  · rw [hp.2,ordinary_induced_spokes_map]
    exact hs.symm
end Oberwolfach
