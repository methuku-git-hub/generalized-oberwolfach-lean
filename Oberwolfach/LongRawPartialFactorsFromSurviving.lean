module

public import Oberwolfach.LongRawPartialFactorsDeletedSafe
public import Oberwolfach.LongRawPartialDomainExcludesLong
public import Oberwolfach.LongRawPartialFactorsAbsorberSafeCount
public import Oberwolfach.LongRawSelectedOrdinaryAvoidsAbsorber
public import Oberwolfach.LongRawSelectedRimPhysical
public import Oberwolfach.LongRawPartialDomains
public import Oberwolfach.LongRawPartialFactorEdgesDisjoint
public import Oberwolfach.LongRawPartialFactorEdgesActive

@[expose] public section
/-! The ordinary partial factors use active raw rims and have pairwise
disjoint physical edge images at distinct hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longPartialAfterDeletionFinDecidable (n:ℕ):DecidableEq (Fin n):=
  longRawRealizationsAvoidAbsorberDecidableEqFin1 n
variable {n K:ℕ} {U X:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]

local instance longRawPartialAfterDeletionSelectedFintype (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e)):
    Fintype (LongRawSelectedOrdinary π d m ℓ e M):=by
  let f:(LongRawSelectedOrdinary π d m ℓ e M)→M:=fun a=>⟨a.val,a.property.1⟩
  have hf:Function.Injective f:=by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun x:M=>x.val) h
  exact Fintype.ofInjective f hf

local instance longRawPartialAfterDeletionAtHubFintype (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e))
    (u:U):Fintype (LongRawSelectedAtHub π d m ℓ e M u):=by
  unfold LongRawSelectedAtHub
  exact Fintype.ofFinite _

theorem long_raw_partial_factors_from_surviving_matching
    (F:U→SimpleGraph (Fin n)) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (d m:ℕ) (ℓ:Fin K→ℕ) (hℓ:∀i,ℓ i≤K)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) t)
    (Reserve:Finset (Finset (Fin n)⊕(Fin n×U))) (X:Finset (Fin n)) (Z:Finset U)
    (Deleted:Finset (Sym2 (Fin n))):
    let selected:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (σ e)
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false t J false false
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let state:=longRawHubState P π d raw true true
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let S:=longRawSurvivingResources P π d raw true true Deleted
    let q:=survivingCandidateEmbedding (mixedCandidateResources R) S (bernoulliVertexSet state)
      (long_raw_surviving_resources_subset P π d raw true true Deleted)
    MarkedFixedTerminalAbsorber P π d m selected H Reserve X Z →
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) (Function.Embedding.subtype (·∈S))),
    (∀c∈M,∀c'∈M,c≠c'→Disjoint (restrictedResourceSet (mixedCandidateResources R) (Function.Embedding.subtype (·∈S)) c)
      (restrictedResourceSet (mixedCandidateResources R) (Function.Embedding.subtype (·∈S)) c')) →
    let N:=M.map q
    LongRawOrdinaryComponentMapsProperty F π d m ℓ e N →
    let A:=LongRawSelectedOrdinary π d m ℓ e N
    let Q:=longRawSelectedOrdinaryWheel π d m ℓ e N
    ∃assign:A↪(Σu,(F u).ConnectedComponent),
    ∃C:∀a:A,(F (Q a).val.2).ConnectedComponent,
      (∀a,(⟨(Q a).val.2,C a⟩:Σu,(F u).ConnectedComponent)=assign a) ∧
    (∀u,Fintype.card (longRawSourceDomain F π d m ℓ e N C u) =
      ∑i:Fin K,(N.filter (fun c=>c.val.1=some i ∧
        longRawSeedHub π d m ℓ c.val.1 c.val.2=u)).card * ℓ i) ∧
    (∀u,Fintype.card {v:Fin n // v∉longRawSourceDomain F π d m ℓ e N C u} =
      n - ∑i:Fin K,(N.filter (fun c=>c.val.1=some i ∧
        longRawSeedHub π d m ℓ c.val.1 c.val.2=u)).card * ℓ i) ∧
    (∀u v,K<Fintype.card ((F u).connectedComponentMk v)→
      v∉longRawSourceDomain F π d m ℓ e N C u) ∧
    let T:=longRawSourceDomain F π d m ℓ e N C
    ∃ψ:∀u,(T u)↪Fin n,
      (∀u x y,(F u).Adj x.val y.val→
        rawMarkedPairRims P π d raw (Sum.inl (ψ u x,ψ u y)) ∨
        rawMarkedPairRims P π d raw (Sum.inl (ψ u y,ψ u x))) ∧
      (∀u v,u≠v→Disjoint
        (partialFactorPhysicalEdges (T u) ((F u).induce (T u)) (ψ u))
        (partialFactorPhysicalEdges (T v) ((F v).induce (T v)) (ψ v))) ∧
      (∀u x y,(F u).Adj x.val y.val→Sum.inl ({ψ u x,ψ u y}:Finset (Fin n))∉Reserve) ∧
      (∀u x y,(F u).Adj x.val y.val→s(ψ u x,ψ u y)∉Deleted) :=by
  intro selected H raw state e R S q habs M hmatch N hprop A Q
  have hm := (long_raw_surviving_matching_lift P π d m ℓ raw true true Deleted M (by
    intro c hc c' hc' hne
    convert hmatch c hc c' hc' hne using 1 <;> congr 3 <;> exact Subsingleton.elim _ _)).1
  have hm': ∀c∈N,∀c'∈N,c≠c'→Disjoint
      (restrictedResourceSet (mixedCandidateResources R) e c)
      (restrictedResourceSet (mixedCandidateResources R) e c'):=by
    intro c hc c' hc' hne
    convert hm c hc c' hc' hne using 1 <;> congr 3 <;> exact Subsingleton.elim _ _
  have hd := long_raw_surviving_ordinary_rim_avoids_deleted P π d m ℓ raw true true Deleted M
  exact long_raw_partial_factors_deleted_safe_and_exclude_long F P π d m ℓ hℓ σ t J Reserve X Z Deleted habs N hm' hprop hd
end Oberwolfach
