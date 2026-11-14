module

public import Oberwolfach.OrdinaryInducedFinsetTransfer
public import Oberwolfach.EndpointPairingHostTransfer
public import Oberwolfach.EndpointPairingGraph

@[expose] public section
/-! Endpoint assignments on an induced physical domain lift to the
ambient graph, retaining their original endpoint sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

def ordinaryInducedFinsetEquiv (T A:Finset V) (hAT:A⊆T):
    {v:{v:V // v∈T} // v∈ordinaryInducedFinset T A} ≃ {v:V // v∈A} where
  toFun x:=⟨x.val.val,(Finset.mem_filter.mp x.property).2⟩
  invFun x:=⟨⟨x.val,hAT x.property⟩,by simp [ordinaryInducedFinset,x.property]⟩
  left_inv x:=by apply Subtype.ext;apply Subtype.ext;rfl
  right_inv x:=by apply Subtype.ext;rfl

def ordinaryInducedEndpointPairingLift
    (G F:SimpleGraph V) (T A B:Finset V) (hAT:A⊆T) (hBT:B⊆T)
    (hdis:Disjoint A B)
    (P:EndpointPairing (G.induce (T:Set V)) (F.induce (T:Set V))
      (ordinaryInducedFinset T A) (ordinaryInducedFinset T B)):
    EndpointPairing G F A B where
  disjoint_parts:=hdis
  left:=(ordinaryInducedFinsetEquiv T B hBT).symm.toEmbedding.trans
    (P.left.trans (ordinaryInducedFinsetEquiv T A hAT).toEmbedding)
  right:=(ordinaryInducedFinsetEquiv T B hBT).symm.toEmbedding.trans
    (P.right.trans (ordinaryInducedFinsetEquiv T A hAT).toEmbedding)
  adjacent:=by
    intro u
    let ui:{u:{v:V // v∈T} // u∈ordinaryInducedFinset T B}:=
      (ordinaryInducedFinsetEquiv T B hBT).symm u
    have hh:=P.adjacent ui
    change G.Adj (P.left ui).val.val ui.val.val ∧ G.Adj (P.right ui).val.val ui.val.val at hh
    exact hh
  avoid:=by
    intro u
    let ui:{u:{v:V // v∈T} // u∈ordinaryInducedFinset T B}:=
      (ordinaryInducedFinsetEquiv T B hBT).symm u
    have hh:=P.avoid ui
    change ¬F.Adj (P.left ui).val.val (P.right ui).val.val at hh
    exact hh
  disjoint_ranges:=by
    apply Set.disjoint_left.mpr
    intro x hx hy
    obtain ⟨u,hu⟩:=hx
    obtain ⟨v,hv⟩:=hy
    have he: P.left ((ordinaryInducedFinsetEquiv T B hBT).symm u)=
        P.right ((ordinaryInducedFinsetEquiv T B hBT).symm v):=by
      apply (ordinaryInducedFinsetEquiv T A hAT).injective
      exact hu.trans hv.symm
    exact Set.disjoint_left.mp P.disjoint_ranges ⟨_,rfl⟩ ⟨_,he.symm⟩
  cover:=by
    intro v
    let vi:{v:{v:V // v∈T} // v∈ordinaryInducedFinset T A}:=
      (ordinaryInducedFinsetEquiv T A hAT).symm v
    rcases P.cover vi with ⟨u,hu⟩|⟨u,hu⟩
    · left
      refine ⟨ordinaryInducedFinsetEquiv T B hBT u,?_⟩
      simpa [vi] using congrArg (ordinaryInducedFinsetEquiv T A hAT) hu
    · right
      refine ⟨ordinaryInducedFinsetEquiv T B hBT u,?_⟩
      simpa [vi] using congrArg (ordinaryInducedFinsetEquiv T A hAT) hu

theorem ordinary_induced_endpoint_pairing_avoiding_lift
    (G F D:SimpleGraph V) (T A B:Finset V) (hAT:A⊆T) (hBT:B⊆T)
    (hdis:Disjoint A B)
    (P:EndpointPairing (G.induce (T:Set V)) (F.induce (T:Set V))
      (ordinaryInducedFinset T A) (ordinaryInducedFinset T B))
    (havoid:Disjoint P.graph (D.induce (T:Set V))):
    ∃P':EndpointPairing G F A B,Disjoint P'.graph D:=by
  have hsub:P.graph≤(G.induce (T:Set V))\(D.induce (T:Set V)):=
    endpoint_pairing_survives_deletion _ _ _ _ _ _ P havoid le_rfl
  let Pdel:=endpointPairingToHost _ _ _ _ _ P hsub
  have hp:EndpointPairing ((G\D).induce (T:Set V)) (F.induce (T:Set V))
      (ordinaryInducedFinset T A) (ordinaryInducedFinset T B):=Pdel
  let Plift:=ordinaryInducedEndpointPairingLift (G\D) F T A B hAT hBT hdis hp
  exact EndpointPairing.deleted_graph_choice G D F A B ⟨Plift⟩
end Oberwolfach
