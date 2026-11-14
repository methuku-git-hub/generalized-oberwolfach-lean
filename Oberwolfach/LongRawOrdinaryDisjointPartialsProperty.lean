module

public import Oberwolfach.LongRawPartialFactorsDisjoint

@[expose] public section
/-! The source domains and physically edge-disjoint ordinary partial factor
maps produced on one supplied raw sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

def LongRawOrdinaryDisjointPartialsProperty
    (F:U→SimpleGraph (Fin n)) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (d m:ℕ) (ℓ:Fin K→ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),Prop :=by
  intro state e R M
  exact
    let A:=LongRawSelectedOrdinary π d m ℓ e M
    let Q:=longRawSelectedOrdinaryWheel π d m ℓ e M
    ∃assign:A↪(Σu,(F u).ConnectedComponent),
    ∃C:∀a:A,(F (Q a).val.2).ConnectedComponent,
      (∀a,(⟨(Q a).val.2,C a⟩:Σu,(F u).ConnectedComponent)=assign a) ∧
    let T:=longRawSourceDomain F π d m ℓ e M C
    ∃ψ:∀u,(T u)↪Fin n,
      (∀u x y,(F u).Adj x.val y.val→
        rawMarkedPairRims P π d raw (Sum.inl (ψ u x,ψ u y)) ∨
        rawMarkedPairRims P π d raw (Sum.inl (ψ u y,ψ u x))) ∧
      (∀u v,u≠v→Disjoint
        (partialFactorPhysicalEdges (T u) ((F u).induce (T u)) (ψ u))
        (partialFactorPhysicalEdges (T v) ((F v).induce (T v)) (ψ v)))
end Oberwolfach
