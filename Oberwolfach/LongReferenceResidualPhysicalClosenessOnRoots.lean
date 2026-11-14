module

public import Oberwolfach.LongReferenceLossDegreeOnRoots
public import Oberwolfach.LongResidualSurplusFromCommonEvent
public import Oberwolfach.LongReferenceLossDegreeBound
public import Oberwolfach.GraphChangedDegreeSides
public import Oberwolfach.LongUsedSubgraphSmall

@[expose] public section
/-! The actual corrected class residual is a bounded physical edit of the
selected reference, using the same matching and completed packing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_reference_residual_physical_closeness_on_roots
    {n:ℕ} {U C:Type} [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]
    (P S Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (g j:Bool) (R:C→Finset (LongRawHubResource n U)) (a γ δ ξ θ u err N:ℝ) (Roots:Finset (Fin n))
    (hγ:0≤γ) (hCardU:Fintype.card U≤n) (hDel:∀x,(Del.degree x:ℝ)≤δ)
    (hθ:0≤θ) (hu:u≤2*θ)
    (hcolour:∀x,|((sampledColourDegree P (fun e=>(σ (Sum.inl e)).1) 4 x):ℝ)-u*(P.degree x:ℝ)|≤err)
    (hEdit:∀x,((changed ((longPhysicalStateGraph P σ {0,1,2,3,4}).neighborFinset x) (S.neighborFinset x)).card:ℝ)≤ξ*n):
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let Q:=longRawSurvivingResources P π d raw g j Del.edgeFinset
    let q:=survivingCandidateEmbedding R Q T (long_raw_surviving_resources_subset P π d raw g j Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g j;
    ∀(M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈Q))))
      (Pack:Finset (Sym2 (Fin n))) (E:U→Finset (Sym2 (Fin n))),
    let Used:=physicalRimCandidateUnion φ (restrictedResourceSet R (Function.Embedding.subtype (·∈T))) (M.map q)
    let Small:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔prescribedPhysicalUnion E
    let Sel:=longSelectedPhysicalGraph P π d σ;
    Pack=Used.edgeFinset→Pack⊆(longApproximatePhysicalGraph P π d σ).edgeFinset→
    (∀v∈Roots,((prescribedPhysicalUnion E).degree v:ℝ)≤N)→
    (∀i,((longRawIncidenceSet Q i\M.biUnion (restrictedResourceSet R (Function.Embedding.subtype (·∈Q)))).card:ℝ)≤
      max (a*n) (γ*(longRawIncidenceSet Q i).card))→
    ∀v∈Roots,((changed (Sel.neighborFinset v) ((S\Small).neighborFinset v)).card:ℝ)≤
      (2*θ+2*max a (4*γ)+2*ξ)*n+N+err+δ+2*(6*d+2:ℕ):=by
  intro raw T Q q φ M Pack E Used Small Sel hPack hApprox hNew hmatch v hv
  have hUsed:Used≤Small:=long_used_subgraph_small Used Pack E hPack
  have hsurplus:=long_residual_surplus_from_common_event P S Small Del π d σ g j R a γ δ ξ θ u err
    hγ hCardU hDel hθ hu hcolour hEdit M hUsed hmatch v
  have hloss:=long_reference_loss_degree_bound_on_roots P S π d σ Pack E hApprox Roots ξ N hEdit hNew v hv
  have hsides:((changed (Sel.neighborFinset v) ((S\Small).neighborFinset v)).card:ℝ)≤
      ((Sel\(S\Small)).degree v:ℝ)+(((S\Small)\Sel).degree v:ℝ):=by
    have hn:(changed (Sel.neighborFinset v) ((S\Small).neighborFinset v)).card≤
        (Sel\(S\Small)).degree v+((S\Small)\Sel).degree v:=by
      convert graph_changed_degree_le_sides Sel (S\Small) v using 1 <;> congr!
    exact_mod_cast hn
  have hloss':((Sel\(S\Small)).degree v:ℝ)≤ξ*n+N:=by
    convert hloss using 1 <;> congr!
  have hsurplus':(((S\Small)\Sel).degree v:ℝ)≤
      2*θ*n+err+2*max a (4*γ)*n+δ+2*(6*d+2:ℕ)+ξ*n:=by
    convert hsurplus using 1 <;> congr!
  nlinarith [hloss',hsurplus',hsides]
end Oberwolfach
