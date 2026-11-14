module

public import Oberwolfach.OrdinaryFixedVortexNonrootNumericInputsLateLoad
public import Oberwolfach.OrdinaryVortexSupportedNonrootCoverFromBalance
public import Oberwolfach.OrdinaryFixedVortexCleanupBalance
public import Oberwolfach.OrdinaryNonrootWheelCoverResult
public import Oberwolfach.OrdinaryFixedVortexConflictDegree
public import Oberwolfach.OrdinaryVortexSupportedLocalExactBalance
public import Oberwolfach.OrdinaryFixedVortexRimCutTransport
public import Oberwolfach.OrdinaryFixedVortexDeepCoverEvent
public import Oberwolfach.MarkedFixedVortexAmbientBounds

@[expose] public section
/-! The nonroot cover applies at any vortex parent supporting the balanced
host, including the initial parent and all protected later parents. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_supported_nonroot_cover_original_numeric
    (mWheel K:ℕ) (hm:3≤mWheel) (ρ₀ pmin href δlimit a ρ θ:ℝ)
    (hρ₀:0<ρ₀) (hpmin:0<pmin) (hhref:0<href) (hδlimit:0<δlimit)
    (ha:0<a) (hρ:0<ρ) (hθ:0<θ):
    ∃δcut ζcut εcut ζlimit εsample εvortex:ℝ,
      0<δcut ∧ δcut<1/4 ∧ δcut≤δlimit ∧ 0<ζcut ∧ 0<εcut ∧ 0<ζlimit ∧
      0<εsample ∧ 0<εvortex ∧ εvortex<1/4 ∧
    ∀ε:ℝ,0<ε→ε≤εvortex→∀aLoad:ℝ,0<aLoad→aLoad≤1→∀β:ℝ,0≤β→β≤1/4→∀d:ℕ,
    ∃ξ η₀:ℝ,0<ξ ∧ 0<η₀ ∧ ∃v₀:ℕ,1≤v₀ ∧ ∀η:ℝ,0≤η→η≤η₀→
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U],
    ∀(P G:SimpleGraph V) (Hs:V→U→Prop) (D vsize:ℕ),
      P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (σ:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool) (j:Color) (s:U→Color→ℝ)
      (i:ℕ),i<Q.length→
    ∀(pR pH density εR εH Ledit βe βh αcut pstar θhost αhost:ℝ),
    let f:markedVortexVertexType Q i↪V:=(markedVortexVertexEmbedding Q i).toEmbedding;
    let g:=markedVortexHubEmbedding Q i;let I:=markedVortexInnerVertices Q i;let T:=markedVortexDeeperVertices Q i;
    let B:=markedVortexInnerHubs Q i;let W:=markedVortexDeeperHubs Q i;
    let ρi:=markedVortexPermutation Q π hπ i;
    let Ploc:=P.comap f;let Floc:=(permutationConflictGraph π (3*d)).comap f;
    let Gloc:=G.comap f;let Hloc:=fun v u=>Hs (f v) (g u);
    let localRaw:=ordinaryRawRestrictPair f g σ;
    let localCoins:=fun e:Sym2 (markedVortexVertexType Q i)=>coins (Sym2.map f e);
    pmin≤pH→εR≤εsample→εH≤εsample→Ledit≤ζlimit*I.card→
    OrdinaryCleanupParentProfiles Ploc Gloc Floc Hloc ρi d I B pR pH density (εR*I.card) (εH*B.card) Ledit βe βh (fun u=>s (g u)) j localRaw→
    density=θhost+αhost-β/2→0≤εR→0≤εH→(θhost+αhost)*Fintype.card V≤D→
    pR=initialIndexDensity U D*pH→
    OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D vsize β ε Q π hπ pR pH s j σ→
    (initialIndexDensity U D*pH)*β*I.card+εR*I.card+2*(εH*B.card)+3*Ledit≤η*I.card→
    G≤P→ ordinaryHostResources G Hs⊆ordinaryRootResources (Q.extendedVertices i) (Q.extendedIndices i)→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→(∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    OrdinaryFixedVortexDeepCoverEvent mWheel K d a aLoad ρ θ P D vsize β ε Q π hπ j σ→
    OrdinaryInducedRimCutEvent (Q.extendedVertices (i+1)) (sampledOrientation (rawWheelGraph P σ) coins) αcut pstar→
    0<pH→pH≤1→0≤εcut→0≤ζcut→0≤ζlimit→0≤Ledit→
    δcut≤min (αcut/32) (pstar/512)→href≤αcut*pstar/64→
    OrdinaryNonrootWheelCoverResult mWheel K ξ aLoad Gloc Floc Hloc I T B W :=by
  obtain ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,hδ,hδsmall,hδcap,hζ,hεcut,hζlimit,hεsample,hεv,hεv1,hnum⟩:=
    ordinary_fixed_vortex_nonroot_numeric_inputs_late_load ρ₀ pmin href δlimit a ρ θ hρ₀ hpmin hhref hδlimit ha hρ hθ
  refine ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,hδ,hδsmall,hδcap,hζ,hεcut,hζlimit,hεsample,hεv,hεv1,?_⟩
  intro ε hε hεvortex aLoad haLoad haLoad1 β hβ hβ1 d
  let ξ:ℝ:=min (ε/200) (aLoad^2/160)
  have hξ:0<ξ:=by dsimp [ξ];positivity
  have hξε:ξ≤ε/100:=by
    have hh:=min_le_left (ε/200) (aLoad^2/160)
    dsimp [ξ];linarith
  have hξsmall:80*ξ≤aLoad^2:=by
    have hh:=min_le_right (ε/200) (aLoad^2/160)
    have hh0:0≤aLoad^2:=sq_nonneg _
    dsimp [ξ];linarith
  obtain ⟨η₀,hη₀,n₀,hcover⟩:=ordinary_vortex_supported_nonroot_cover_from_balance mWheel K hm ρ₀ ε δcut ξ
    hρ₀ hε hδ hδsmall hξ hξε
  obtain ⟨v₀,hv₀,hnum⟩:=hnum ε hε hεvortex aLoad haLoad β hβ hβ1 d n₀
  refine ⟨ξ,η₀,hξ,hη₀,v₀,hv₀,?_⟩
  intro η hη hη0 V U Γ Color _ _ _ _ _ _ P G Hs D vsize hreg hn hD hρlo hρhi hvsize
    Q π hπ σ coins j s i hi pR pH density εR εH Ledit βe βh αcut pstar θhost αhost
    f g I T B W ρi Ploc Floc Gloc Hloc localRaw localCoins hpmin' hεRcap hεHcap hLcap hprofile
    hdensity hεR hεH hdegree hpEq hgood hmargin hGP hsupport hbal hdiv hDeep hRim hpH hpH1 hεcut0 hζcut0 hζlimit0 hLedit hδlim hhrefCap
  have hnums:=hnum V U P D vsize hreg hn hD hρlo hρhi hvsize Q π hπ i hi pH εR εH Ledit hpmin' hεR hεRcap hεH hεHcap hLedit hLcap
  have hv:0<vsize:=by omega
  exact hcover η hη hη0 V U Γ Color P G Hs D vsize β hreg hn hD hρlo hρhi hβ hβ1 hv
    Q π hπ σ coins d j s i hi a aLoad ρ θ ζlimit pR pH density εR εH Ledit βe βh ζcut εcut href αcut pstar θhost αhost
    (by convert hnums using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hprofile hdensity hεR hεH hdegree hpEq hgood hmargin
    hGP hsupport hbal hdiv hDeep hRim hpH hpH1 hεcut0 hζcut0 hζlimit0 hLedit hδlim hhrefCap haLoad haLoad1 hξsmall
end Oberwolfach
