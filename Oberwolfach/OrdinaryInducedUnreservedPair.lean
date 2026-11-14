module

public import Oberwolfach.OrdinaryUnreservedPackingCertificate
public import Oberwolfach.OrdinaryInducedPairEmbedding

@[expose] public section
/-! Reserving and restricting commute: the induced unreserved rim and
spokes are exactly the restrictions of the ambient unreserved pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_induced_unreserved_pair (Q:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (R:SimpleGraph (V⊕U)):
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    let φ:A↪V:=⟨Subtype.val,Subtype.val_injective⟩;
    let ψ:B↪U:=⟨Subtype.val,Subtype.val_injective⟩;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X);
    let Zf:Finset B:=Finset.univ.filter (fun u=>u.val∈Z);
    let Rf:=R.comap (φ.sumMap ψ);
    ordinaryUnreservedRim (Q.induce (A:Set V)) Xf Rf=(ordinaryUnreservedRim Q X R).induce (A:Set V) ∧
    ordinaryUnreservedSpokes (fun (v:A) (u:B)=>H v.val u.val) Xf Zf Rf=
      (fun (v:A) (u:B)=>ordinaryUnreservedSpokes H X Z R v.val u.val):=by
  intro A B φ ψ Xf Zf Rf
  constructor
  · ext v w
    simp only [ordinaryUnreservedRim,SimpleGraph.sdiff_adj,spanningRestriction_adj,SimpleGraph.induce_adj,
      SimpleGraph.comap_adj,Finset.mem_filter,Finset.mem_univ,true_and,Xf,Rf,φ,ψ] <;> rfl
  · funext v u
    apply propext
    simp only [ordinaryUnreservedSpokes,SimpleGraph.comap_adj,Finset.mem_filter,Finset.mem_univ,true_and,
      Xf,Zf,Rf,φ,ψ] <;> rfl
end Oberwolfach
