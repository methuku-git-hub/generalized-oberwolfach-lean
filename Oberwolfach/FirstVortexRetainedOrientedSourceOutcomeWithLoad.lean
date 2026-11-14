module

public import Oberwolfach.LongSelectedRetainedOrientedSourceWithLoad
public import Oberwolfach.LongRetainedProtectedInnerTargets
public import Oberwolfach.LongSelectedExactOrientedSourceOutcome
public import Oberwolfach.LongSelectedExactOrientedSourceWithLoad
public import Oberwolfach.LongSelectedOrientedSourceOutcome
public import Oberwolfach.LongSelectedExactOrientedSourceWithLoad
public import Oberwolfach.LongSelectedExactOrientedSourceOutcome
public import Oberwolfach.LongSelectedExactOrientedSourceWithLoad
public import Oberwolfach.FirstVortexActualSourceCompleteMatchingLoad
public import Oberwolfach.LongSelectedExactOrientedSourceOutcome
public import Oberwolfach.LongSelectedExactOrientedSourceWithLoad

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstMatchingRetainedOrientedSourceOutcomeLoadFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem first_vortex_retained_oriented_source_outcome_with_complete_matching_load
    (α lam ε δ θ eps ξ:ℝ) (d K m:ℕ)
    (hα:0<α) (hlam:0<lam) (hε:0<ε) (hδ:0<δ) (hθ:0<θ)
    (hθδ:10*θ≤δ) (hθlocal:θ≤δ/32) (hθhi:θ≤1/100)
    (hlamlocal:lam≤δ*ε/32) (hspacing:1/(d:ℝ)≤θ/1024)
    (hd:3≤d) (hK:1≤K) (hm:1≤m)
    (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hξ:4*ξ≤eps/2):
    ∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (ℓ:Fin K→ℕ)
    (Dv mm:ℕ) (β:ℝ) (Vort:Vortex U P Dv β ε mm)
    (hreg:P.IsRegularOfDegree Dv) (hDv:0<Dv) (hρhi:initialIndexDensity U Dv≤1) (hU:0<Fintype.card U) (hmm:0<mm)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (DelG:SimpleGraph (Fin n)) (D:Fin n→Fin n→Prop) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t),
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σE e)
    let Del:=DelG.edgeFinset
    let H:=Vort.extendedIndices 1
    let A:=Vort.extendedVertices 1
    let σ:=fun e=>raw (Sum.inr e)
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let S:=longRawSurvivingResources P π d raw true true Del
    let hST:=long_raw_surviving_resources_subset P π d raw true true Del
    let q:=survivingCandidateEmbedding R S T hST
    let Q:=restrictedResourceSet R (Function.Embedding.subtype (·∈S))
    ∀(M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S)))),
    let Used:=physicalRimCandidateUnion (markedRawSampledPhysicalEmbedding P π d raw true true)
      (restrictedResourceSet R (Function.Embedding.subtype (·∈T))) (M.map q)
    let P₀:=longPhysicalStateGraph P σE {0,1,2,3,4}\Used
    let Sel:=longSelectedPhysicalGraph P π d σE
    let Kbad:=longRequiredPhysicalGraph P P₀ Sel π d A D (fun x y=>Used.Adj x y)
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (C₀ a γ δDel:ℝ) (hC:1≤C₀) (hehi:ε≤α/(1000*C₀)) (hlamhi:lam≤α/128)
    (hγ:0≤γ) (ha:a≤lam/(10*d)) (hγrate:γ≤lam/(10*d))
    (hDel:∀x,(DelG.degree x:ℝ)≤δDel) (hδDel:δDel≤ξ*n)
    (hrow:∀v∈A,|(((P.neighborFinset v∩A).filter (fun w=>(σE (Sum.inl s(v,w))).1=4)).card:ℝ)-
      (2*(∑w:U,(1-(1/100:ℝ)-(1/100:ℝ)/(m:ℝ)-longAssignedApproxMarkedWeight F hF K m θ w-longAssignedApproxOrdinaryWeight F hF K m θ w))/(Dv:ℝ))*(P.neighborFinset v∩A).card|<(n:ℝ)^(3/4:ℝ))
    (hmatch:∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card))
    (hboundary:∀v∈A,((rawIntervalBoundaryHubSet π d σ H v).card:ℝ)≤4*(H.card:ℝ)/d+4*(A.card:ℝ)^(3/4:ℝ))
    (absorber:U→Finset (Fin n))
    (ζ ρ:ℝ) (hζ:ζ≤θ/4096) (hρ:ρ≤θ/4096) (hζ0:0≤ζ)
    (hscale:max a γ*n≤ρ*A.card)
    (hrows:RetainedRestrictionLocalGood π d σ false t A H ζ Jret)
    (hfixed:∀w∈H,|rawIntervalUnassignedHubCountOn π d σ w A-
      (A.card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(A.card:ℝ)^(3/4:ℝ))
    (hcolumn:∀v∈A,|rawIntervalUnassignedColumnCount π d σ v H-
      ∑w∈H,(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(A.card:ℝ)^(3/4:ℝ))
    (hsource:LongSelectedRetainedOrientedSourceOutcome hU F P π d m ℓ raw t Jret σE (M.map q)),
    LongSelectedRetainedOrientedSourceWithLoad hU F P π d m ℓ raw t Jret σE H A Kbad absorber δ (M.map q) :=by
  obtain ⟨N,hN⟩:=first_vortex_actual_source_complete_matching_load α lam ε δ θ eps ξ d K m hα hlam hε hδ hθ hθδ hθlocal hθhi hlamlocal hspacing hd hK hm heps hξ
  refine ⟨N,?_⟩
  intro n hn U _ _ P π ℓ Dv mm β Vort hreg hDv hρhi hU hmm σE DelG D t Jret raw Del H A σ R T S hST q Q M Used P₀ Sel Kbad F hF C₀ a γ δDel hC hehi hlamhi hγ ha hγrate hDel hδDel hrow hmatch hboundary absorber ζ ρ hζ hρ hζ0 hscale hrows hfixed hcolumn hsource
  unfold LongSelectedRetainedOrientedSourceOutcome at hsource
  obtain ⟨Dsrc,orig,hpair,hcycles,hwhole,hArcs,E,halign,hres,ext,paths,ψ,assign,data,hprops,pieces,hgraph,harcs,Pack,hdis,hsub,hLayer,hAvoid,hExact,hEq,hhub,hsize⟩:=hsource
  have hpropsOld := fun w:U => by
    rcases hprops w with ⟨hc,hd0,hs1,hC,hsupp,hinner,hmarker,hocc,hdisj,hinj,hold,hreserved,hs2,ht,hT,hlen,hverts,hOrd,hMarked,hMarkedEdges,hOrdEdges,hPathDisjoint,hRootAvoid,hOrientation,hOldDirected⟩
    have hreservedOld := hreserved.mono_right
      (raw_ordinary_outer_subset_retained π d (fun e=>raw (Sum.inr e)) false t Jret false false w)
    exact And.intro hc (And.intro hd0 (And.intro hs1 (And.intro hC (And.intro hsupp (And.intro hinner (And.intro hmarker (And.intro hocc (And.intro hdisj (And.intro hinj (And.intro hold (And.intro hreservedOld (And.intro hs2 (And.intro ht (And.intro hT (And.intro hlen (And.intro hverts (And.intro hOrd (hMarked))))))))))))))))))
  have hpropsBase := fun w:U => by
    rcases hprops w with ⟨hc,hd0,hs1,hC,hsupp,hinner,hmarker,hocc,hdisj,hinj,hold,hreserved,hs2,ht,hT,hlen,hverts,hOrd,hMarked,_,_,hPathDisjoint,hRootAvoid,hOrientation,hOldDirected⟩
    exact And.intro hc (And.intro hd0 (And.intro hs1 (And.intro hC (And.intro hsupp (And.intro hinner (And.intro hmarker (And.intro hocc (And.intro hdisj (And.intro hinj (And.intro hold (And.intro hreserved (And.intro hs2 (And.intro ht (And.intro hT (And.intro hlen (And.intro hverts (And.intro hOrd (And.intro hMarked (And.intro hPathDisjoint (And.intro hRootAvoid (And.intro hOrientation (hOldDirected))))))))))))))))))))))
  have hload:=hN n hn U P π ℓ Dv mm β Vort hreg hDv hρhi hmm σE DelG D t Jret M F hF assign hhub data ext ψ E paths C₀ a γ δDel hC hehi hlamhi hγ ha hγrate hDel hδDel hrow hmatch hboundary absorber ζ ρ hζ hρ hζ0 hscale hrows hfixed hcolumn hpropsOld
  unfold LongSelectedRetainedOrientedSourceWithLoad
  exact ⟨Dsrc,orig,hpair,hcycles,hwhole,hArcs,E,halign,hres,ext,paths,ψ,assign,data,hpropsBase,hload,pieces,hgraph,harcs,Pack,hdis,hsub,hLayer,hAvoid,hExact,hEq,hhub,hsize⟩
end Oberwolfach
