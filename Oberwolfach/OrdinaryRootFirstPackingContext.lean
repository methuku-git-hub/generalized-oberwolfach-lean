module

public import Oberwolfach.OrdinaryRootFreeUnreservedMap
public import Oberwolfach.OrdinaryPackingCleanupData

@[expose] public section
/-! Concrete data for the root-first packing step. The packing is on the
actual nonroot subtype and uses the pullback of the ambient reserve graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

structure OrdinaryRootFirstPackingContext (Q F:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t:ℝ) where
  root_sub:T⊆X
  hub_sub:W⊆Z
  cover:OrdinaryRootCoverData Q F H X T Z W r η ell
  reserve:SimpleGraph (V⊕U)
  packing:
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    let φ:A↪V:=⟨Subtype.val,Subtype.val_injective⟩;
    let ψ:B↪U:=⟨Subtype.val,Subtype.val_injective⟩;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X);
    let Zf:Finset B:=Finset.univ.filter (fun u=>u.val∈Z);
    let Rf:=reserve.comap (φ.sumMap ψ);
    let Q':=Q\cover.rim;let H':=fun v u=>H v u∧¬cover.spokes v u;
    OrdinaryUnreservedPackingData (Q'.induce (A:Set V)) (F.induce (A:Set V))
      (fun (v:A) (u:B)=>H' v.val u.val) Xf Zf Rf r t
end Oberwolfach
