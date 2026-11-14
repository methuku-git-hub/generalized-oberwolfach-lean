module

public import Oberwolfach.OrdinaryRootFirstPackingContext
public import Oberwolfach.OrdinaryInducedPackingLeftoverGeneric
public import Oberwolfach.OrdinaryPackingLeftoverBound

@[expose] public section
/-! The lifted nonroot packing leaves only the controlled-degree physical
remainder of the actual ambient unreserved target. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_first_packing_leftover
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t:ℝ)
    (K:OrdinaryRootFirstPackingContext Q F H X T Z W r η ell t) (ht:0≤t):
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    let φ:A↪V:=⟨Subtype.val,Subtype.val_injective⟩;
    let ψ:B↪U:=⟨Subtype.val,Subtype.val_injective⟩;
    let Q':=Q\K.cover.rim;let H':=fun v u=>H v u∧¬K.cover.spokes v u;
    let D:=(ordinaryWheelRimGraph K.packing.wheels).map φ;
    let E:=ordinaryMappedSpokes (ordinaryPackingSpokes K.packing.wheels) φ ψ;
    ∀a:V⊕U,(((ordinaryPhysicalGraph (ordinaryUnreservedRim Q' X K.reserve)
      (ordinaryUnreservedSpokes H' X Z K.reserve))\ordinaryPhysicalGraph D E).degree a:ℝ)≤t:=by
  intro A B φ ψ Q' H' D E
  let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X)
  let Zf:Finset B:=Finset.univ.filter (fun u=>u.val∈Z)
  let Rf:=K.reserve.comap (φ.sumMap ψ)
  let Qf:=Q'.induce (A:Set V)
  let Ff:=F.induce (A:Set V)
  let Hf:=fun (v:A) (u:B)=>H' v.val u.val
  let G:=ordinaryUnreservedRim Qf Xf Rf
  let J:=ordinaryUnreservedSpokes Hf Xf Zf Rf
  let Df:=ordinaryWheelRimGraph K.packing.wheels
  let Ef:=ordinaryPackingSpokes K.packing.wheels
  have hleft:=ordinary_unreserved_packing_leftover_bound Qf Ff Hf Xf Zf Rf r t K.packing
  have hlift:=ordinary_induced_packing_leftover_bound_generic G Df J Ef φ ψ t ht hleft
  have hmap:=ordinary_root_free_unreserved_map Q F H X T Z W r η ell K.root_sub K.hub_sub K.cover K.reserve
  have hG:G.map φ=ordinaryUnreservedRim Q' X K.reserve:=hmap.1
  have hJ:ordinaryMappedSpokes J φ ψ=ordinaryUnreservedSpokes H' X Z K.reserve:=hmap.2
  have he:(ordinaryPhysicalGraph (ordinaryUnreservedRim Q' X K.reserve)
      (ordinaryUnreservedSpokes H' X Z K.reserve)\ordinaryPhysicalGraph D E)=
      (ordinaryPhysicalGraph (G.map φ) (ordinaryMappedSpokes J φ ψ)\
        ordinaryPhysicalGraph (Df.map φ) (ordinaryMappedSpokes Ef φ ψ)):=by
    rw [hG,hJ]
  intro a
  apply le_trans ?_ (hlift a)
  have hd:=congrArg (fun S:SimpleGraph (V⊕U)=>(S.degree a:ℝ)) he
  convert le_of_eq hd using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
end Oberwolfach
