module

public import Oberwolfach.OrdinaryVortexTraceBufferedTriangleNonrootCoverFromBalance
public import Oberwolfach.OrdinaryTriangleRootCoverWithinBudget
public import Oberwolfach.OrdinaryTriangleNonrootCoverNumericInputs
public import Oberwolfach.OrdinaryFixedVortexTriangleNonrootCoverEvent
public import Oberwolfach.OrdinaryFixedVortexCleanupBalance
public import Oberwolfach.OrdinaryNonrootWheelCoverResult
public import Oberwolfach.OrdinaryFixedVortexConflictDegree
public import Oberwolfach.OrdinaryVortexTraceLocalExactBalance
public import Oberwolfach.OrdinaryFixedVortexRimCutTransport
public import Oberwolfach.OrdinaryFixedVortexDeepCoverEvent
public import Oberwolfach.OrdinaryProtectedTraceHostLe
public import Oberwolfach.MarkedFixedVortexAmbientBounds

@[expose] public section
/-! At a later protected vortex level, the common deep-cover and rim-cut
sample, local cleanup profile, and global exact balance give the protected
nonroot wheel cover on the actual remainder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_trace_buffered_triangle_root_data_from_balance
    (buffer:ℕ) (hbuffer:2≤buffer) (ρ₀ ε δcut ξ:ℝ)
    (hρ₀:0<ρ₀) (hε:0<ε) (hδ:0<δcut) (hδsmall:δcut<1/4) (hξ:0<ξ) (hξε:ξ≤ε/100):
    ∃η₀:ℝ,0<η₀ ∧ ∃n₀:ℕ,∀η:ℝ,0≤η→η≤η₀→
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U],
    ∀(P JQ G:SimpleGraph V) (JH Hs:V→U→Prop) (D vsize:ℕ) (β:ℝ),
      P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→0≤β→β≤1/4→0<vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (σ:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool) (d:ℕ) (j:Color) (s:U→Color→ℝ)
      (Kres:Finset (Sym2 V⊕(V×U))) (cost deepCost:ℕ→ℝ) (i:ℕ),i+1<Q.length→
    ∀(A:Finset (Sym2 V⊕(V×U))) (κ ζlimit pR pH density εR εH Ledit βe βh ζcut εcut href αcut pstar θhost αhost γ lam:ℝ),
    let f:markedVortexVertexType Q (i+1)↪V:=(markedVortexVertexEmbedding Q (i+1)).toEmbedding;
    let g:=markedVortexHubEmbedding Q (i+1);let I:=markedVortexInnerVertices Q (i+1);let T:=ordinaryVortexBufferedVertices Q (i+1) buffer;
    let B:=markedVortexInnerHubs Q (i+1);let W:=ordinaryVortexBufferedHubs Q (i+1) buffer;
    let ρi:=markedVortexPermutation Q π hπ (i+1);
    let Ploc:=P.comap f;let Floc:=(permutationConflictGraph π (3*d)).comap f;
    let Gloc:=G.comap f;let Hloc:=fun v u=>Hs (f v) (g u);
    let localRaw:=ordinaryRawRestrictPair f g σ;
    let localCoins:=fun e:Sym2 (markedVortexVertexType Q (i+1))=>coins (Sym2.map f e);
    let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j;
    let S:=(R\permutationConflictGraph π (3*d))\JQ;let H:=fun v u=>J v u∧¬JH v u;
    let S₀:=S\ordinaryResourceRim S Kres;let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈Kres);
    let X:=fun k=>Q.extendedVertices (k+1);let Tdeep:=fun k=>Q.extendedVertices (k+buffer);
    let Z:=fun k=>Q.extendedIndices (k+1);let Wdeep:=fun k=>Q.extendedIndices (k+buffer);
    OrdinaryNonrootNumericInputs Floc I T B W n₀ d (ρ₀/8) κ κ κ κ ζlimit ε δcut ζcut εcut pH εR εH Ledit href→
    OrdinaryCleanupParentProfiles Ploc Gloc Floc Hloc ρi d I B pR pH density (εR*I.card) (εH*B.card) Ledit βe βh (fun u=>s (g u)) j localRaw→
    density=θhost+αhost-β/2→0≤εR→0≤εH→(θhost+αhost)*Fintype.card V≤D→
    pR=initialIndexDensity U D*pH→
    OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D vsize β ε Q π hπ pR pH s j σ→
    (initialIndexDensity U D*pH)*β*I.card+εR*I.card+2*(εH*B.card)+3*Ledit≤η*I.card→
    OrdinaryProtectedTrace S₀ H₀ X Tdeep Z Wdeep cost deepCost (i+1) A→ ordinaryHostResources G Hs=A→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→(∀u,3∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    OrdinaryFixedVortexTriangleNonrootCoverEvent d κ P D vsize β ε Q π hπ j σ→
    OrdinaryInducedRimCutEvent (Q.extendedVertices (i+2)) (sampledOrientation (rawWheelGraph P σ) coins) αcut pstar→
    0<pH→pH≤1→0≤εcut→0≤ζcut→0≤ζlimit→0≤Ledit→
    δcut≤min (αcut/32) (pstar/512)→href≤αcut*pstar/64→
    0<κ→κ≤1→80*ξ≤κ^2→
    0<γ→0≤lam→lam≤1/4→κ≤γ/1000→lam≤γ/100→η*ε≤γ/8→
    (T.card:ℝ)+W.card≤lam*Fintype.card (markedVortexVertexType Q (i+1))→
    let Root:=Finset.univ\T;
    let ell:=max (18*κ*Fintype.card (markedVortexVertexType Q (i+1))+3*((W.card:ℝ)+T.card))
      (9*κ*Fintype.card (markedVortexVertexType Q (i+1))+3*(T.card:ℝ));
    let bin:=η*I.card;let fcost:ℝ:=T.card+2*W.card;let binner:=bin+3*ell+fcost;
    Nonempty (OrdinaryRootCoverNonrootData Gloc Floc Hloc I T B W 3 (10*ξ*I.card) ell) ∧
    0≤ell ∧ 0≤bin ∧ 0≤fcost ∧ 0≤binner ∧
    fcost≤γ*Fintype.card Root ∧ binner≤γ*Fintype.card Root ∧ ell≤γ*Fintype.card Root :=by
  obtain ⟨η₀,hη₀,n₀,hmain⟩:=ordinary_vortex_trace_buffered_triangle_nonroot_cover_from_balance buffer hbuffer ρ₀ ε δcut ξ
    hρ₀ hε hδ hδsmall hξ hξε
  refine ⟨η₀,hη₀,n₀,?_⟩
  intro η hη hη0 V U Γ Color _ _ _ _ _ _ P JQ G JH Hs D vsize β hreg hn hD hρlo hρhi hβ hβ1 hvsize
    Q π hπ σ coins d j s Kres cost deepCost i hi A κ ζlimit pR pH density εR εH Ledit βe βh ζcut εcut href αcut pstar θhost αhost γ lam
    f g I T B W ρi Ploc Floc Gloc Hloc localRaw localCoins R J S H S₀ H₀ X Tdeep Z Wdeep
    hnums hprofile hdensity hεR hεH hdegree hpEq hgood hmargin htrace hstate hbal hdiv hDeep hRim hpH hpH1 hεcut hζcut hζlimit hLedit hδlim hhref hκ hκ1 hξsmall
    hγ hlam hlam1 hκcap hlamcap hbalcap hroots Root ell bin fcost binner
  have hcover:=hmain η hη hη0 V U Γ Color P JQ G JH Hs D vsize β hreg hn hD hρlo hρhi hβ hβ1 hvsize
    Q π hπ σ coins d j s Kres cost deepCost i hi A κ ζlimit pR pH density εR εH Ledit βe βh ζcut εcut href αcut pstar θhost αhost
    hnums hprofile hdensity hεR hεH hdegree hpEq hgood hmargin htrace hstate hbal hdiv hDeep hRim hpH hpH1 hεcut hζcut hζlimit hLedit hδlim hhref hκ hκ1 hξsmall
  have hsub:=ordinary_vortex_buffered_nested Q (i+1) buffer hbuffer
  have hI:(I.card:ℝ)≤ε*Fintype.card (markedVortexVertexType Q (i+1)):=by
    have hh:=(Q.extended_successor_size_bounds hε.le (i+1)).1
    simpa only [I,(marked_vortex_inner_cardinalities Q (i+1)).1,markedVortexVertexType,Fintype.card_coe] using hh
  have hh:=ordinary_triangle_root_cover_within_budget Gloc Floc Hloc I T B W ξ κ γ lam η ε
    hsub.2.2.1 hsub.2.2.2 hcover hγ hκ.le hlam hlam1 hη hε.le hI hroots hκcap hlamcap hbalcap
  convert hh using 1 <;> congr! 8 <;> simp only [Fintype.card_coe, Root] <;>
    congr 1 <;> first | (congr 1; ext x; simp) | (ext x; simp)
end Oberwolfach
