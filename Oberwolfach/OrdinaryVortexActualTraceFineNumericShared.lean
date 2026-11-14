module

public import Oberwolfach.OrdinaryFixedVortexNonrootNumericAt
public import Oberwolfach.OrdinaryVortexActualTraceFineCover
public import Oberwolfach.OrdinaryNonrootNumericSmallerDeep
public import Oberwolfach.OrdinaryFixedVortexNonrootNumericInputsLateLoad

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

theorem ordinary_vortex_actual_trace_fine_numeric_shared_before_beta
    (mWheel K buffer:ℕ) (hm:3≤mWheel) (hbuffer:2≤buffer) (ρ₀ pmin href δlimit a ρ θ:ℝ)
    (hρ₀:0<ρ₀) (hpmin:0<pmin) (hhref:0<href) (hδlimit:0<δlimit)
    (ha:0<a) (hρ:0<ρ) (hθ:0<θ):
    ∃δcut ζcut εcut ζlimit εsample εvortex:ℝ,
      0<δcut ∧ δcut<1/4 ∧ δcut≤δlimit ∧ 0<ζcut ∧ 0<εcut ∧ 0<ζlimit ∧
      0<εsample ∧ 0<εvortex ∧ εvortex<1/4 ∧
      OrdinaryFixedVortexNonrootNumericAt ρ₀ pmin href a ρ θ δcut ζcut εcut ζlimit εsample εvortex ∧
    ∀ε:ℝ,0<ε→ε≤εvortex→∀aLoad:ℝ,0<aLoad→aLoad≤1→
    ∃ξ η₀:ℝ,ξ=min (ε/200) (aLoad^2/160) ∧ η₀=δcut*(ρ₀/8)*ξ/1000 ∧ 0<ξ ∧ 0<η₀ ∧ ∀β:ℝ,0≤β→β≤1/4→∀d:ℕ,
    ∃v₀:ℕ,1≤v₀ ∧ ∀η:ℝ,0≤η→η≤η₀→
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U],
    ∀(P Gbase G:SimpleGraph V) (Hbase Hs:V→U→Prop) (D vsize:ℕ),
      Gbase≤P→P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (σ:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool) (j:Color) (s:U→Color→ℝ)
      (Kres:Finset (Sym2 V⊕(V×U))) (cost deepCost:ℕ→ℝ) (i:ℕ),i+1<Q.length→
    ∀(A:Finset (Sym2 V⊕(V×U))) (pR pH density εR εH Ledit βe βh αcut pstar θhost αhost:ℝ),
    let f:markedVortexVertexType Q (i+1)↪V:=(markedVortexVertexEmbedding Q (i+1)).toEmbedding;
    let g:=markedVortexHubEmbedding Q (i+1);let I:=markedVortexInnerVertices Q (i+1);let T:=ordinaryVortexBufferedVertices Q (i+1) buffer;
    let B:=markedVortexInnerHubs Q (i+1);let W:=ordinaryVortexBufferedHubs Q (i+1) buffer;
    let ρi:=markedVortexPermutation Q π hπ (i+1);
    let Ploc:=P.comap f;let Floc:=(permutationConflictGraph π (3*d)).comap f;
    let Gloc:=G.comap f;let Hloc:=fun v u=>Hs (f v) (g u);
    let localRaw:=ordinaryRawRestrictPair f g σ;
    let localCoins:=fun e:Sym2 (markedVortexVertexType Q (i+1))=>coins (Sym2.map f e);
    let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j;
    let S:=Gbase;let H:=Hbase;
    let S₀:=S\ordinaryResourceRim S Kres;let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈Kres);
    let X:=fun k=>Q.extendedVertices (k+1);let Tdeep:=fun k=>Q.extendedVertices (k+buffer);
    let Z:=fun k=>Q.extendedIndices (k+1);let Wdeep:=fun k=>Q.extendedIndices (k+buffer);
    pmin≤pH→εR≤εsample→εH≤εsample→Ledit≤ζlimit*I.card→
    OrdinaryCleanupParentProfiles Ploc Gloc Floc Hloc ρi d I B pR pH density (εR*I.card) (εH*B.card) Ledit βe βh (fun u=>s (g u)) j localRaw→
    density=θhost+αhost-β/2→0≤εR→0≤εH→(θhost+αhost)*Fintype.card V≤D→
    pR=initialIndexDensity U D*pH→
    OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D vsize β ε Q π hπ pR pH s j σ→
    (∀v:I,|((Gloc.induce (I:Set _)).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:B=>Hloc v.val u.val)).card|≤η*I.card)→
    OrdinaryProtectedTrace S₀ H₀ X Tdeep Z Wdeep cost deepCost (i+1) A→ ordinaryHostResources G Hs=A→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→(∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    OrdinaryFixedVortexDeepCoverEvent mWheel K d a aLoad ρ θ P D vsize β ε Q π hπ j σ→
    OrdinaryInducedRimCutEvent (Q.extendedVertices (i+2)) (sampledOrientation (rawWheelGraph P σ) coins) αcut pstar→
    0<pH→pH≤1→0≤εcut→0≤ζcut→0≤ζlimit→0≤Ledit→
    δcut≤min (αcut/32) (pstar/512)→href≤αcut*pstar/64→
    OrdinaryFineWheelCoverResult mWheel K ξ aLoad Gloc Floc Hloc I T B W :=by
  obtain ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,hδ,hδsmall,hδcap,hζ,hεcut,hζlimit,hεsample,hεv,hεv1,hnum⟩:=
    ordinary_fixed_vortex_nonroot_numeric_inputs_late_load ρ₀ pmin href δlimit a ρ θ hρ₀ hpmin hhref hδlimit ha hρ hθ
  refine ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,hδ,hδsmall,hδcap,hζ,hεcut,hζlimit,hεsample,hεv,hεv1,hnum,?_⟩
  intro ε hε hεvortex aLoad haLoad haLoad1
  let ξ:ℝ:=min (ε/200) (aLoad^2/160)
  have hξ:0<ξ:=by dsimp [ξ];positivity
  have hξε:ξ≤ε/100:=by
    have hh:=min_le_left (ε/200) (aLoad^2/160)
    dsimp [ξ];linarith
  have hξsmall:80*ξ≤aLoad^2:=by
    have hh:=min_le_right (ε/200) (aLoad^2/160)
    have hh0:0≤aLoad^2:=sq_nonneg _
    dsimp [ξ];linarith
  obtain ⟨η₀,hηEq,hη₀,n₀,hcover⟩:=ordinary_vortex_actual_trace_fine_cover_from_local_balance mWheel K buffer hbuffer hm ρ₀ ε δcut ξ
    hρ₀ hε hδ hδsmall hξ hξε
  refine ⟨ξ,η₀,rfl,hηEq,hξ,hη₀,?_⟩
  intro β hβ hβ1 d
  obtain ⟨v₀,hv₀,hnum⟩:=hnum ε hε hεvortex aLoad haLoad β hβ hβ1 d n₀
  refine ⟨v₀,hv₀,?_⟩
  intro η hη hη0 V U Γ Color _ _ _ _ _ _ P Gbase G Hbase Hs D vsize hGbase hreg hn hD hρlo hρhi hvsize
    Q π hπ σ coins j s Kres cost deepCost i hi A pR pH density εR εH Ledit βe βh αcut pstar θhost αhost
    f g I T B W ρi Ploc Floc Gloc Hloc localRaw localCoins R J S H S₀ H₀ X Tdeep Z Wdeep
    hpmin' hεRcap hεHcap hLcap hprofile hdensity hεR hεH hdegree hpEq hgood hnear htrace hstate hbal hdiv
    hDeep hRim hpH hpH1 hεcut0 hζcut0 hζlimit0 hLedit hδlim hhrefCap
  have hnums:=hnum V U P D vsize hreg hn hD hρlo hρhi hvsize Q π hπ (i+1) hi pH εR εH Ledit hpmin' hεR hεRcap hεH hεHcap hLedit hLcap
  have hsub:=ordinary_vortex_buffered_nested Q (i+1) buffer hbuffer
  have hnums':OrdinaryNonrootNumericInputs Floc I T B W n₀ d (ρ₀/8) a ρ θ aLoad ζlimit ε δcut ζcut εcut pH εR εH Ledit href:=by
    apply ordinary_nonroot_numeric_inputs_smaller_deep Floc I (markedVortexDeeperVertices Q (i+1)) T B
      (markedVortexDeeperHubs Q (i+1)) W n₀ d (ρ₀/8) a ρ θ aLoad ζlimit ε δcut ζcut εcut pH εR εH Ledit href
      hsub.1 hsub.2.1
    convert hnums using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  exact hcover η hη hη0 V U Γ Color P Gbase G Hbase Hs D vsize β hGbase hreg hn hD hρlo hρhi hβ hβ1 (by omega)
    Q π hπ σ coins d j s Kres cost deepCost i hi A a aLoad ρ θ ζlimit pR pH density εR εH Ledit βe βh ζcut εcut href αcut pstar θhost αhost
    hnums' hprofile hdensity hεR hεH hdegree hpEq hgood hnear htrace hstate hbal hdiv hDeep hRim hpH hpH1 hεcut0 hζcut0 hζlimit0 hLedit hδlim hhrefCap haLoad haLoad1 hξsmall
end Oberwolfach
