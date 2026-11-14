module

public import Oberwolfach.OrdinaryRootFirstPackingLeftover
public import Oberwolfach.OrdinaryRootFirstPackingSubhost
public import Oberwolfach.OrdinaryPhysicalGraphDeletion

@[expose] public section
/-! The root-first packing supplies the exact physical host and the
unreserved remainder needed by the deep-avoiding cleanup. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_first_cleanup_facts
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t:ℝ)
    (K:OrdinaryRootFirstPackingContext Q F H X T Z W r η ell t) (ht:0≤t)
    (σ:Sym2 (V⊕U)→Bool)
    (hreserve:K.reserve=retainedGraph (ordinaryBoundaryGraph (Q\K.cover.rim)
      (fun v u=>H v u∧¬K.cover.spokes v u) X Z) σ):
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    let φ:A↪V:=⟨Subtype.val,Subtype.val_injective⟩;
    let ψ:B↪U:=⟨Subtype.val,Subtype.val_injective⟩;
    let Q':=Q\K.cover.rim;let H':=fun v u=>H v u∧¬K.cover.spokes v u;
    let D:=(ordinaryWheelRimGraph K.packing.wheels).map φ;
    let E:=ordinaryMappedSpokes (ordinaryPackingSpokes K.packing.wheels) φ ψ;
    let C:=ordinaryPhysicalGraph D E;
    ordinaryPhysicalGraph (Q'\D) (fun v u=>H' v u∧¬E v u)=ordinaryPhysicalGraph Q' H'\C ∧
    (∀a:V⊕U,((((ordinaryPhysicalGraph Q' H'\spanningRestriction (ordinaryPhysicalGraph Q' H')
      (ordinaryInnerVertices X Z))\retainedGraph (ordinaryBoundaryGraph Q' H' X Z) σ)\C).degree a:ℝ)≤t):=by
  intro A B φ ψ Q' H' D E C
  constructor
  · ext a b
    cases a with
    | inl v=>cases b with
      | inl w=>rfl
      | inr u=>rfl
    | inr u=>cases b with
      | inl v=>rfl
      | inr u'=>simp [ordinaryPhysicalGraph]
  · have h:=ordinary_root_first_packing_leftover Q F H X T Z W r η ell t K ht
    have he:((ordinaryPhysicalGraph Q' H'\spanningRestriction (ordinaryPhysicalGraph Q' H')
        (ordinaryInnerVertices X Z))\retainedGraph (ordinaryBoundaryGraph Q' H' X Z) σ)\C=
        ordinaryPhysicalGraph (ordinaryUnreservedRim Q' X K.reserve)
        (ordinaryUnreservedSpokes H' X Z K.reserve)\C:=by
      rw [ordinary_unreserved_physical_graph,hreserve]
    intro a
    apply le_trans ?_ (h a)
    have hd:=congrArg (fun S:SimpleGraph (V⊕U)=>(S.degree a:ℝ)) he
    convert le_of_eq hd using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
end Oberwolfach
