module

public import Oberwolfach.OrdinaryVortexSupportedTriangleFineCover
public import Oberwolfach.OrdinaryFixedVortexNonrootNumericAt
public import Oberwolfach.OrdinaryNonrootNumericSmallerDeep

@[expose] public section
/-! Reuse the preselected numeric geometry to obtain a fine cover on an
arbitrary supported actual host, including the initial vortex parent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_supported_triangle_fine_cover_shared_numeric
    (buffer:ℕ) (hbuffer:2≤buffer)
    (ρ₀ pmin href κ δcut ζcut εcut ζlimit εsample εvortex:ℝ)
    (hρ₀:0<ρ₀) (hδ:0<δcut) (hδsmall:δcut<1/4)
    (hnum:OrdinaryFixedVortexNonrootNumericAt ρ₀ pmin href κ κ κ δcut ζcut εcut ζlimit εsample εvortex)
    (ε ξ aLoad η β:ℝ) (d:ℕ) (hε:0<ε) (hεvortex:ε≤εvortex)
    (haLoad:0<aLoad) (haLoad1:aLoad≤1) (hξEq:ξ=min (ε/200) (aLoad^2/160))
    (hη:0≤η) (hηcap:η≤δcut*(ρ₀/8)*ξ/1000) (hβ:0≤β) (hβ1:β≤1/4):
    ∃v₀:ℕ,1≤v₀ ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U],
    ∀(P G:SimpleGraph V) (Hs:V→U→Prop) (D vsize:ℕ),
      G≤P→P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (σ:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool) (j:Color) (s:U→Color→ℝ)
      (i:ℕ),i<Q.length→
    ∀(pR pH density εR εH Ledit βe βh αcut pstar θhost αhost:ℝ),
    let f:markedVortexVertexType Q i↪V:=(markedVortexVertexEmbedding Q i).toEmbedding;
    let g:=markedVortexHubEmbedding Q i;let I:=markedVortexInnerVertices Q i;let T:=ordinaryVortexBufferedVertices Q i buffer;
    let B:=markedVortexInnerHubs Q i;let W:=ordinaryVortexBufferedHubs Q i buffer;
    let ρi:=markedVortexPermutation Q π hπ i;
    let Ploc:=P.comap f;let Floc:=(permutationConflictGraph π (3*d)).comap f;
    let Gloc:=G.comap f;let Hloc:=fun v u=>Hs (f v) (g u);
    let localRaw:=ordinaryRawRestrictPair f g σ;
    let localCoins:=fun e:Sym2 (markedVortexVertexType Q i)=>coins (Sym2.map f e);
    pmin≤pH→εR≤εsample→εH≤εsample→Ledit≤ζlimit*I.card→
    OrdinaryCleanupParentProfiles Ploc Gloc Floc Hloc ρi d I B pR pH density (εR*I.card) (εH*B.card) Ledit βe βh (fun u=>s (g u)) j localRaw→
    0≤εR→0≤εH→
    (∀v:I,|((Gloc.induce (I:Set _)).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:B=>Hloc v.val u.val)).card|≤η*I.card)→
    ordinaryHostResources G Hs⊆ordinaryRootResources (Q.extendedVertices i) (Q.extendedIndices i)→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→(∀u,3∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    OrdinaryFixedVortexTriangleSeparateLoadFineCoverEvent d κ aLoad P D vsize β ε Q π hπ j σ→
    OrdinaryInducedRimCutEvent (Q.extendedVertices (i+1)) (sampledOrientation (rawWheelGraph P σ) coins) αcut pstar→
    0<pH→pH≤1→0≤εcut→0≤ζcut→0≤ζlimit→0≤Ledit→
    δcut≤min (αcut/32) (pstar/512)→href≤αcut*pstar/64→
    OrdinaryFineWheelCoverResult 2 0 ξ aLoad Gloc Floc Hloc I T B W :=by
  have hξ:0<ξ:=by rw [hξEq];positivity
  have hξε:ξ≤ε/100:=by
    rw [hξEq]
    have hh:=min_le_left (ε/200) (aLoad^2/160)
    linarith
  have hξsmall:80*ξ≤aLoad^2:=by
    rw [hξEq]
    have hh:=min_le_right (ε/200) (aLoad^2/160)
    have hh0:0≤aLoad^2:=sq_nonneg _
    linarith
  obtain ⟨η₀,hηEq,hη₀,n₀,hcover⟩:=ordinary_vortex_supported_triangle_fine_cover_local_balance_explicit buffer hbuffer ρ₀ ε δcut ξ
    hρ₀ hε hδ hδsmall hξ hξε
  have hη0:η≤η₀:=by rw [hηEq];exact hηcap
  obtain ⟨v₀,hv₀,hnum⟩:=hnum ε hε hεvortex aLoad haLoad β hβ hβ1 d n₀
  refine ⟨v₀,hv₀,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P G Hs D vsize hGP hreg hn hD hρlo hρhi hvsize
    Q π hπ σ coins j s i hi pR pH density εR εH Ledit βe βh αcut pstar θhost αhost
    f g I T B W ρi Ploc Floc Gloc Hloc localRaw localCoins
    hpmin' hεRcap hεHcap hLcap hprofile hεR hεH hnear hsupport hbal hdiv
    hDeep hRim hpH hpH1 hεcut0 hζcut0 hζlimit0 hLedit hδlim hhrefCap
  have hnums:=hnum V U P D vsize hreg hn hD hρlo hρhi hvsize Q π hπ i hi pH εR εH Ledit hpmin' hεR hεRcap hεH hεHcap hLedit hLcap
  have hsub:=ordinary_vortex_buffered_nested Q i buffer hbuffer
  have hnums':OrdinaryNonrootNumericInputs Floc I T B W n₀ d (ρ₀/8) κ κ κ aLoad ζlimit ε δcut ζcut εcut pH εR εH Ledit href:=by
    apply ordinary_nonroot_numeric_inputs_smaller_deep Floc I (markedVortexDeeperVertices Q i) T B
      (markedVortexDeeperHubs Q i) W n₀ d (ρ₀/8) κ κ κ aLoad ζlimit ε δcut ζcut εcut pH εR εH Ledit href
      hsub.1 hsub.2.1
    convert hnums using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  exact hcover η hη hη0 V U Γ Color P G Hs D vsize β hGP hreg hn hD hρlo hρhi hβ hβ1 (by omega)
    Q π hπ σ coins d j s i hi κ aLoad ζlimit pR pH density εR εH Ledit βe βh ζcut εcut href αcut pstar θhost αhost
    hnums' hprofile hnear hsupport hbal hdiv hDeep hRim hpH hpH1 hεcut0 hζcut0 hζlimit0 hLedit hδlim hhrefCap haLoad haLoad1 hξsmall
end Oberwolfach
