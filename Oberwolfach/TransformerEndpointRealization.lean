module

public import Oberwolfach.CanonicalEdgeDarts
public import Oberwolfach.TransformerPathEndpoints
public import Oberwolfach.TransformerEndpointAssignments

@[expose] public section

/-! Realize the degree-balance endpoint bijection using the actual,
disjoint rim and spoke paths. Both endpoint maps are injective and their
images are disjoint, so the prescribed pairs are disjoint. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

 def spokeEndpointEquiv (G:SimpleGraph V) (H:V→U→Prop)
    (b:∀ v,G.neighborSet v≃({u:U // H v u}×Fin 2)):
    (Σ v,G.neighborSet v)≃({e:V×U // H e.1 e.2}×Fin 2) where
  toFun d:=(⟨(d.1,(b d.1 d.2).1.val),(b d.1 d.2).1.property⟩,(b d.1 d.2).2)
  invFun z:=⟨z.1.val.1,(b z.1.val.1).symm (⟨z.1.val.2,z.1.property⟩,z.2)⟩
  left_inv:=by rintro ⟨v,w⟩;simp
  right_inv:=by rintro ⟨⟨⟨v,u⟩,h⟩,i⟩;simp

 theorem transformer_endpoint_realization (G Q:SimpleGraph V) (H:V→U→Prop)
    (b:∀ v,G.neighborSet v≃({u:U // H v u}×Fin 2))
    (p:(G.edgeFinset⊕{e:V×U // H e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c))
    (hp:∀ i,(p i).2.2.IsPath) (hlen:∀ i,0<(p i).2.2.length)
    (hdis:∀ i j,i≠j→Disjoint (p i).2.2.support.toFinset (p j).2.2.support.toFinset):
    let E:=(neighborSigmaDartEquiv G).trans (canonicalEdgeDartEquiv G).symm
    let J:=spokeEndpointEquiv G H b
    let a:(Σ v,G.neighborSet v)→V:=fun d=>graphPathEndpoint (p (.inl (E d).1)) (E d).2
    let z:(Σ v,G.neighborSet v)→V:=fun d=>graphPathEndpoint (p (.inr (J d).1)) (J d).2
    Function.Injective a ∧ Function.Injective z ∧ (∀ d d',a d≠z d') ∧
      (∀ d,a d≠z d) ∧ ∀ d d',d≠d'→Disjoint ({a d,z d}:Finset V) {a d',z d'}:=by
  dsimp only
  let E:=(neighborSigmaDartEquiv G).trans (canonicalEdgeDartEquiv G).symm
  let J:=spokeEndpointEquiv G H b
  let a:(Σ v,G.neighborSet v)→V:=fun d=>graphPathEndpoint (p (.inl (E d).1)) (E d).2
  let z:(Σ v,G.neighborSet v)→V:=fun d=>graphPathEndpoint (p (.inr (J d).1)) (J d).2
  have hpoint:=disjoint_path_endpoint_injective p hp hlen hdis
  have ha:Function.Injective a:=by
    intro d e he
    have hh:=hpoint (a₁ := (Sum.inl (E d).1,(E d).2)) (a₂ := (Sum.inl (E e).1,(E e).2)) he
    have h1:(E d).1=(E e).1:=Sum.inl.inj (Prod.mk.inj hh).1
    have h2:(E d).2=(E e).2:=(Prod.mk.inj hh).2
    exact E.injective (Prod.ext h1 h2)
  have hz:Function.Injective z:=by
    intro d e he
    have hh:=hpoint (a₁ := (Sum.inr (J d).1,(J d).2)) (a₂ := (Sum.inr (J e).1,(J e).2)) he
    have h1:(J d).1=(J e).1:=Sum.inr.inj (Prod.mk.inj hh).1
    have h2:(J d).2=(J e).2:=(Prod.mk.inj hh).2
    exact J.injective (Prod.ext h1 h2)
  have haz:∀ d e,a d≠z e:=by
    intro d e he
    have hh:=hpoint (a₁ := (Sum.inl (E d).1,(E d).2)) (a₂ := (Sum.inr (J e).1,(J e).2)) he
    exact Sum.inl_ne_inr ((Prod.mk.inj hh).1)
  have hh:=paired_endpoint_sets_disjoint a z ha hz haz
  exact ⟨ha,hz,haz,hh.1,hh.2⟩

end Oberwolfach
