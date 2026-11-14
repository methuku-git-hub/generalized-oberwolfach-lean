module

public import Oberwolfach.OrdinaryVortexTriangleRootDataTraceError
public import Oberwolfach.OrdinaryTriangleRootErrorBudget

@[expose] public section
/-! Choose the root-cover error after the load and trace rate but before
    the common sample, retaining the actual local packing conclusion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_triangle_root_error_chosen_after_load
    (ρ₀ ε δcut α p traceRate aRef cap:ℝ)
    (hρ₀:0<ρ₀) (hα:0<α) (hp:0<p) (hp1:p≤1) (hε:0<ε) (hδ:0<δcut) (hδsmall:δcut<1/4)
    (htrace:0<traceRate) (haRef:0<aRef) (hcap:0<cap):
    ∃ξ:ℝ,0<ξ ∧ ξ≤ε/100 ∧ 80*ξ≤aRef^2 ∧ 10*ξ≤traceRate ∧ ξ≤cap ∧
    ∃η₀:ℝ,0<η₀ ∧ ∃n₀:ℕ,∀η:ℝ,0≤η→η≤η₀→
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U],
    ∀(P G:SimpleGraph V) (Hs:V→U→Prop) (D vsize:ℕ) (β:ℝ),
      P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→0≤β→β≤1/4→0<vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (σ:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool) (d:ℕ) (j:Color) (s:U→Color→ℝ)
      (i:ℕ),i<Q.length→
    ∀(a b ζlimit pR pH density εR εH Ledit βe βh ζcut εcut href αcut pstar ηrow θ ρ ρhub θhost δrate:ℝ),
    let f:markedVortexVertexType Q i↪V:=(markedVortexVertexEmbedding Q i).toEmbedding;
    let g:=markedVortexHubEmbedding Q i;let I:=markedVortexInnerVertices Q i;let T:=markedVortexDeeperVertices Q i;
    let B:=markedVortexInnerHubs Q i;let W:=markedVortexDeeperHubs Q i;
    let ρi:=markedVortexPermutation Q π hπ i;
    let Ploc:=P.comap f;let Floc:=(permutationConflictGraph π (3*d)).comap f;
    let Gloc:=G.comap f;let Hloc:=fun v u=>Hs (f v) (g u);
    let localRaw:=ordinaryRawRestrictPair f g σ;
    let localCoins:=fun e:Sym2 (markedVortexVertexType Q i)=>coins (Sym2.map f e);
    OrdinaryNonrootNumericInputs Floc I T B W n₀ d (ρ₀/8) b b b a ζlimit ε δcut ζcut εcut pH εR εH Ledit href→
    0≤b→ε≤b→ε≤ρ₀/16→β≤α/8→
    1/2≤θhost→cycleThreshold 3≤θhost→(θhost+α)*Fintype.card V≤D→
    (∀x k,0<k→k<2*d+1→(π^k) x≠x)→p≤pR→pR≤1→p≤pH→pH≤1→pR=initialIndexDensity U D*pH→
    6*b≤p^6*(min (α/2) 1)/4→6*b≤(p^6*(min (α/2) 1)/4)*(ρ₀/16)→
    b≤p^6*(min (α/2) 1)/8→b≤(p^6*(min (α/2) 1)/8)*(ρ₀/16)→
    b+12*a≤ρhub→3*b+24*a≤ρ/2→b≤θ→
    (((2*(3*d):ℕ):ℝ)+2*(3*d:ℕ))≤ρ*Fintype.card (markedVortexVertexType Q i)/2→
    0≤ηrow→β+2*b≤2*(ρ₀/16)*p*ηrow→
    18*a*Fintype.card (markedVortexVertexType Q i)+3*((W.card:ℝ)+T.card)≤δrate*I.card→
    9*a*Fintype.card (markedVortexVertexType Q i)+3*(T.card:ℝ)≤δrate*I.card→
    OrdinaryCleanupParentProfiles Ploc Gloc Floc Hloc ρi d I B pR pH density (εR*I.card) (εH*B.card) Ledit βe βh (fun u=>s (g u)) j localRaw→
    (∀v:I,|(((Gloc.induce (I:Set _)).degree v):ℝ)-2*(Finset.univ.filter (fun u:B=>Hloc v.val u.val)).card|≤η*I.card)→
    G≤P→ ordinaryHostResources G Hs⊆ordinaryRootResources (Q.extendedVertices i) (Q.extendedIndices i)→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→(∀u,3∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    (∀i,i<Q.length→
      let f:=markedVortexVertexEmbedding Q i;let g:=markedVortexHubEmbedding Q i;
      let ρi:=markedVortexPermutation Q π hπ i;let B:=markedVortexInnerHubs Q i;
      let localRaw:=ordinaryRawRestrictPair f g σ;
      OrdinaryTriangleSeparatedCoverEvent (P.comap f) ((permutationConflictGraph π (3*d)).comap f)
        ρi d (2*(3*d)) B a p (min (α/2) 1) ρhub pR pH ηrow θ ρ j localRaw)→
    OrdinaryInducedRimCutEvent (Q.extendedVertices (i+1)) (sampledOrientation (rawWheelGraph P σ) coins) αcut pstar→
    0<pH→pH≤1→0≤εcut→0≤ζcut→0≤ζlimit→0≤Ledit→
    δcut≤min (αcut/32) (pstar/512)→href≤αcut*pstar/64→
    0<a→a≤1→80*ξ≤a^2→
    Nonempty (OrdinaryRootCoverNonrootData Gloc Floc Hloc I T B W 3 (10*ξ*I.card) (δrate*I.card)) ∧
    10*ξ*(I.card:ℝ)≤traceRate*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i) :=by
  obtain ⟨ξ,hξ,hξε,hξa,hξtrace,hξcap,hAll⟩:=ordinary_triangle_root_error_budget ε aRef traceRate cap hε haRef htrace hcap
  obtain ⟨η₀,hη₀,n₀,hmain⟩:=ordinary_vortex_supported_triangle_root_data_trace_error ρ₀ ε δcut ξ α p traceRate
    hρ₀ hα hp hp1 hε hδ hδsmall hξ hξε hξtrace
  exact ⟨ξ,hξ,hξε,hξa,hξtrace,hξcap,η₀,hη₀,n₀,hmain⟩
end Oberwolfach
