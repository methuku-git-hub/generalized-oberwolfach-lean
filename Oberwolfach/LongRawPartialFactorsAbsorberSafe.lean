module

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
local instance longPartialAvoidFinDecidable (n:ℕ):DecidableEq (Fin n):=
  longRawRealizationsAvoidAbsorberDecidableEqFin1 n
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_partial_factors_disjoint_and_absorber_safe
    (F:U→SimpleGraph (Fin n)) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (d m:ℕ) (ℓ:Fin K→ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) t)
    (Reserve:Finset (Finset (Fin n)⊕(Fin n×U))) (X:Finset (Fin n)) (Z:Finset U):
    let selected:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (σ e)
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false t J false false
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let state:=longRawHubState P π d raw true true
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    MarkedFixedTerminalAbsorber P π d m selected H Reserve X Z →
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    (∀c∈M,∀c'∈M,c≠c'→Disjoint (restrictedResourceSet (mixedCandidateResources R) e c)
      (restrictedResourceSet (mixedCandidateResources R) e c')) →
    LongRawOrdinaryPartialFactorsProperty F π d m ℓ e M →
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
        (partialFactorPhysicalEdges (T v) ((F v).induce (T v)) (ψ v))) ∧
      (∀u x y,(F u).Adj x.val y.val→Sum.inl ({ψ u x,ψ u y}:Finset (Fin n))∉Reserve) :=by
  intro selected H raw state e R habs M hmatch hprop A Q
  obtain ⟨assign,C,hC,f,hspoke,hper⟩:=hprop
  let T:=longRawSourceDomain F π d m ℓ e M C
  have hper':∀u,∃ψ:(T u)↪Fin n,
      ∀x y,(F u).Adj x.val y.val→∃a:LongRawSelectedAtHub π d m ℓ e M u,
        longRawSelectedRimRelation π d m ℓ e M a.val (ψ x) (ψ y):=by
    intro u
    obtain ⟨ψ,_,hR⟩:=hper u
    exact ⟨ψ,hR⟩
  choose ψ hψ using hper'
  refine ⟨assign,C,hC,ψ,?_,?_⟩
  · intro u x y hxy
    obtain ⟨a,ha⟩:=hψ u x y hxy
    exact long_raw_partial_factor_edges_active P π d m ℓ raw true true M (ψ u x) (ψ u y) ⟨a.val,ha⟩
  · constructor
    · apply long_raw_partial_factor_edges_disjoint P π d m ℓ raw true true M (by
        intro c hc c' hc' hne
        convert hmatch c hc c' hc' hne using 1 <;> congr 3 <;> exact Subsingleton.elim _ _)
        (fun u=>(T u)) (fun u=>(F u).induce (T u)) (fun u=>ψ u)
      intro u x y hxy
      obtain ⟨a,ha⟩:=hψ u x y hxy
      exact ⟨a.val,a.property,ha⟩
    · intro u x y hxy hreserve
      obtain ⟨a,ha⟩:=hψ u x y hxy
      have hm:=long_raw_selected_rim_physical_resource π d m ℓ e M a.val (ψ u x) (ψ u y) ha
      have hd:=long_raw_selected_ordinary_avoids_fixed_absorber P π d m σ t J Reserve X Z ℓ habs M a.val
      apply (Finset.disjoint_left.mp hd) hm
      convert hreserve using 1 <;> congr 3 <;> exact Subsingleton.elim _ _
end Oberwolfach
