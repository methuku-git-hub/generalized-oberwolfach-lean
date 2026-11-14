module

public import Oberwolfach.LongRawAssignedPartialGraphEmbeddings

@[expose] public section
/-! Assigned ordinary raw wheels yield injective per-factor partial vertex
maps, and every edge in their source domains maps to a selected rim edge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U X:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]

def LongRawOrdinaryPartialFactorsProperty (F:U→SimpleGraph (Fin n))
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ) (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e)):Prop:=
  let A:=LongRawSelectedOrdinary π d m ℓ e M
  let Q:=longRawSelectedOrdinaryWheel π d m ℓ e M
  ∃assign:A↪(Σu,(F u).ConnectedComponent),
  ∃C:∀a:A,(F (Q a).val.2).ConnectedComponent,
  (∀a,(⟨(Q a).val.2,C a⟩:Σu,(F u).ConnectedComponent)=assign a) ∧
  ∃f:∀a:A,C a↪Fin n,
    (∀a x,Sum.inr (f a x,(Q a).val.2)∈orderedOrdinaryResources (Q a).val) ∧
    ∀u,
      let B:Type:={a:A // (Q a).val.2=u}
      let D:B→(F u).ConnectedComponent:=fun a=>
        factorComponentAtAssignedHub F ⟨(Q a.val).val.2,C a.val⟩ u a.property
      let fB:∀a:B,D a↪Fin n:=fun a=>
        (factorComponentHubEquiv F ⟨(Q a.val).val.2,C a.val⟩ u a.property).toEmbedding.trans (f a.val)
      ∃ψ:{v:Fin n // ∃a:B,v∈(D a).supp}↪Fin n,
        (∀a (x:D a),ψ ⟨x.val,⟨a,x.property⟩⟩=fB a x) ∧
        (∀x y,(F u).Adj x.val y.val→
          ∃a:B,longRawSelectedRimRelation π d m ℓ e M a.val (ψ x) (ψ y))

theorem long_raw_component_maps_to_partial_factors
    (F:U→SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e))
    (h:LongRawOrdinaryComponentMapsProperty F π d m ℓ e M):
    LongRawOrdinaryPartialFactorsProperty F π d m ℓ e M :=by
  obtain ⟨assign,C,hC,f,_,_,hR,hspoke,hdis⟩:=h
  refine ⟨assign,C,hC,f,hspoke,?_⟩
  apply long_raw_assigned_partial_graph_embeddings F π d m ℓ e M assign C hC f ?_ hdis
  intro a x y hxy
  exact hR a x y hxy
end Oberwolfach
