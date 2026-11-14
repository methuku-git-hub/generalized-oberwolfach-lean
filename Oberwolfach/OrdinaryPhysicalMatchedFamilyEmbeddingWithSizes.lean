module

public import Oberwolfach.OrdinaryPhysicalMatchedPartialEmbedding

@[expose] public section
/-! Use the same physical matching and its component assignments to obtain
all hubwise partial embeddings simultaneously. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_physical_matched_family_embedding_with_sizes
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (RM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (L:Finset (PhysicalSampledCandidate (mixedCandidateResources
      (ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W))) state))
    (i₀:Fin K) (Cres:∀u,Finset (F u).ConnectedComponent):
    let R:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π
    let A:=fun u=>OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u
    let payload:=fun u=>ordinaryPhysicalUnmarkedPayload π d m RM state L u;
    (∀x∈L,∀y∈L,x≠y→Disjoint (physicalSampledCandidateSet φ (mixedCandidateResources R) state x)
      (physicalSampledCandidateSet φ (mixedCandidateResources R) state y))→
    (∀u,∃f:A u↪↥(Finset.univ\Cres u),∀a,Fintype.card (f a).val=(a.val.val.1.getD i₀).val+1)→
    ∀u,∃f:A u↪↥(Finset.univ\Cres u),
      (∀a,Fintype.card (f a).val=(a.val.val.1.getD i₀).val+1) ∧
      ∃g:∀a,(f a).val↪Fin n,
        (∀a,Set.range (g a)=Set.range (payload u a).2.1.val) ∧
        (∀a (x y:(f a).val),(f a).val.toSimpleGraph.Adj x y↔
          (ordinaryWheelRim (orderedOrdinaryUniversalWheel (by have h:=long_padded_seed_exponent_positive (payload u a).1;omega) (payload u a).2)).Adj (g a x) (g a y)) ∧
      ∃ψ:{v:Fin n // ∃a,v∈((f a).val).supp}↪Fin n,
        ∀a (x:(f a).val),ψ ⟨x.val,⟨a,x.property⟩⟩=g a x :=by
  intro R φ A payload hL hAssign u
  obtain ⟨f,hsize⟩:=hAssign u
  refine ⟨f,hsize,?_⟩
  have hh:=ordinary_physical_matched_partial_embedding F hF π d m RM state L u i₀ (Cres u) f hsize hL
  convert hh using 1 <;> congr! 5
end Oberwolfach
