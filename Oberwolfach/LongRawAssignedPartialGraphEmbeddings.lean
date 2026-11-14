module

public import Oberwolfach.LongRawOrdinaryComponentMapsProperty
public import Oberwolfach.AssignedFactorPartialGraphEmbeddings

@[expose] public section
/-! Glue the assigned raw ordinary wheels at each hub into an injective
partial map, preserving every source edge as an edge of one selected rim. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U X:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]

def longRawSelectedRimRelation (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e))
    (a:LongRawSelectedOrdinary π d m ℓ e M) (x y:Fin n):Prop:=
  let Q:=longRawSelectedOrdinaryWheel π d m ℓ e M a
  let r:=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a).1
  ∃i:Fin r,(x=Q.val.1.val i ∧ y=Q.val.1.val (cycleNext i)) ∨
    (y=Q.val.1.val i ∧ x=Q.val.1.val (cycleNext i))

theorem long_raw_assigned_partial_graph_embeddings
    (F:U→SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e)):
    let A:=LongRawSelectedOrdinary π d m ℓ e M
    let Q:=longRawSelectedOrdinaryWheel π d m ℓ e M
    ∀(assign:A↪(Σu,(F u).ConnectedComponent))
      (C:∀a:A,(F (Q a).val.2).ConnectedComponent),
      (∀a,(⟨(Q a).val.2,C a⟩:Σu,(F u).ConnectedComponent)=assign a) →
    ∀(f:∀a:A,C a↪Fin n),
      (∀a x y,(C a).toSimpleGraph.Adj x y→longRawSelectedRimRelation π d m ℓ e M a (f a x) (f a y)) →
      (∀a a',a≠a'→(Q a).val.2=(Q a').val.2→
        Disjoint (Finset.univ.image (f a)) (Finset.univ.image (f a'))) →
    ∀u,
      let B:Type:={a:A // (Q a).val.2=u}
      let D:B→(F u).ConnectedComponent:=fun a=>
        factorComponentAtAssignedHub F ⟨(Q a.val).val.2,C a.val⟩ u a.property
      let fB:∀a:B,D a↪Fin n:=fun a=>
        (factorComponentHubEquiv F ⟨(Q a.val).val.2,C a.val⟩ u a.property).toEmbedding.trans (f a.val)
      ∃ψ:{v:Fin n // ∃a:B,v∈(D a).supp}↪Fin n,
        (∀a (x:D a),ψ ⟨x.val,⟨a,x.property⟩⟩=fB a x) ∧
        (∀x y,(F u).Adj x.val y.val→
          ∃a:B,longRawSelectedRimRelation π d m ℓ e M a.val (ψ x) (ψ y)) :=by
  intro A Q assign C hC f hR hdis u B D fB
  exact assigned_factor_partial_graph_embeddings F (fun a=>(Q a).val.2) C assign hC f hdis
    (longRawSelectedRimRelation π d m ℓ e M) hR u
end Oberwolfach
