module

public import Oberwolfach.OrdinaryAllHubReservedPaths
public import Oberwolfach.OrdinaryPhysicalMatchedPartialEmbedding

@[expose] public section
/-! The same physical matching's assigned short components can be embedded
while the sampled interval requests receive disjoint source-factor paths. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U A B:Type} [Fintype U] [DecidableEq U] [Fintype A] [Fintype B]

theorem ordinary_matched_reserved_path_compatibility
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (hn:0<n)
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (hd:0<d) (θ:ℝ) (hθ:0<θ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t) (u:U)
    (index : A ⊕ B ≃ retainedAndRawIntervalIndex π d (fun e=>raw (Sum.inr e)) false true t J u)
    (hcut:5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K+1)≤θ/2)
    (hlarge:4*((m:ℝ)+1)/(θ*(θ/100))<(n:ℝ)^((1:ℝ)/4))
    (hcounts:∀g,|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) u-
      (n:ℝ)*ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) u g/d|<(n:ℝ)^(3/4:ℝ)/d)
    (hsupport:∀g v,rawMarkedPairSpokes π d raw g true true v u→
      ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) u g≠0)
    (RM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (L:Finset (PhysicalSampledCandidate (mixedCandidateResources
      (ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W))) state))
    (i₀:Fin K) (Cres:Finset (F u).ConnectedComponent)
    (assign:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u↪↥(Finset.univ\Cres))
    (hsize:∀a,Fintype.card (assign a).val=(a.val.val.1.getD i₀).val+1):
    let R:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π
    let payload:=ordinaryPhysicalUnmarkedPayload π d m RM state L u
    let components:=fun a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u=>(assign a).val
    let I:={C:(F u).ConnectedComponent // K<Fintype.card C}
    let longs:I↪(F u).ConnectedComponent:=Function.Embedding.subtype _;
    (∀x∈L,∀y∈L,x≠y→Disjoint (physicalSampledCandidateSet φ (mixedCandidateResources R) state x)
      (physicalSampledCandidateSet φ (mixedCandidateResources R) state y))→
    ∃g:∀a,components a↪Fin n,
      (∀a,Set.range (g a)=Set.range (payload a).2.1.val) ∧
      (∀a (x y:components a),(components a).toSimpleGraph.Adj x y↔
        (ordinaryWheelRim (orderedOrdinaryUniversalWheel (by have h:=long_padded_seed_exponent_positive (payload a).1;omega) (payload a).2)).Adj (g a x) (g a y)) ∧
    ∃ψ:{v:Fin n // ∃a,v∈(components a).supp}↪Fin n,
      (∀a (x:components a),ψ ⟨x.val,⟨a,x.property⟩⟩=g a x) ∧
    ∃block:A⊕B↪LongReservedBlockIndex (F u) longs (m+1) d,
    ∃ext:∀a:A⊕B,Fin ((m+1)*d+5)↪Fin n,
    ∃inner:∀a:A⊕B,Fin ((m+1)*d+1)↪Fin n,
      (∀a (j:Fin ((m+1)*d+4)),(F u).Adj (ext a ⟨j.val,by omega⟩) (ext a ⟨j.val+1,by omega⟩)) ∧
      (∀a j,inner a j=ext a ⟨j.val+2,by omega⟩) ∧
      (∀a j,ext a j∈(longs (block a).1).supp) ∧
      (∀a b,a≠b→Disjoint (Finset.univ.image (ext a)) (Finset.univ.image (ext b))) ∧
      (∀a j z,ext a j∉(components z).supp) :=by
  intro R φ payload components I longs hL
  obtain ⟨g,hg,hiso,ψ,hψ⟩:=ordinary_physical_matched_partial_embedding F hF π d m RM state L u i₀ Cres assign hsize hL
  obtain ⟨block,ext,inner,hadj,hinner,hmem,hdis,havoid⟩:=
    ordinary_all_hub_reserved_paths F hF hn π d m hd θ hθ raw t J u index hcut hlarge hcounts hsupport
  refine ⟨g,hg,hiso,ψ,hψ,block,ext,inner,hadj,hinner,hmem,hdis,?_⟩
  intro a j z
  apply havoid a j (components z)
  rw [hsize z]
  have hlt:((z.val.val.1.getD i₀).val)<K:=(z.val.val.1.getD i₀).isLt
  omega
end Oberwolfach
