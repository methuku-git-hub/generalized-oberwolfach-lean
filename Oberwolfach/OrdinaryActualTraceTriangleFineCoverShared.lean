module

public import Oberwolfach.OrdinaryVortexSupportedTriangleFineSharedNumeric
public import Oberwolfach.OrdinaryProtectedTraceHostLe
public import Oberwolfach.OrdinaryActualTraceBalanceAndFineCoverAt

@[expose] public section
/-! The shared triangle fine-cover hierarchy also applies to an actual
protected trace; its support follows from the trace on the same host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryActualTraceTriangleFineCoverAtLocalBalance
    (buffer:ℕ) (ρ₀ pmin href δcut ζcut εcut ζlimit εsample ε ξ aLoad κ β η:ℝ)
    (d m₀:ℕ):Prop :=
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U],
    ∀(P Gbase G:SimpleGraph V) (Hbase Hs:V→U→Prop) (D vsize:ℕ),
      Gbase≤P→P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤vsize→
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
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→(∀u,(2+1)∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    OrdinaryFixedVortexTriangleSeparateLoadFineCoverEvent d κ aLoad P D vsize β ε Q π hπ j σ→
    OrdinaryInducedRimCutEvent (Q.extendedVertices (i+2)) (sampledOrientation (rawWheelGraph P σ) coins) αcut pstar→
    0<pH→pH≤1→0≤εcut→0≤ζcut→0≤ζlimit→0≤Ledit→
    δcut≤min (αcut/32) (pstar/512)→href≤αcut*pstar/64→
    OrdinaryFineWheelCoverResult 2 0 ξ aLoad Gloc Floc Hloc I T B W


theorem ordinary_actual_trace_triangle_fine_cover_shared_numeric
    (buffer:ℕ) (hbuffer:2≤buffer)
    (ρ₀ pmin href κ δcut ζcut εcut ζlimit εsample εvortex:ℝ)
    (hρ₀:0<ρ₀) (hδ:0<δcut) (hδsmall:δcut<1/4)
    (hnum:OrdinaryFixedVortexNonrootNumericAt ρ₀ pmin href κ κ κ δcut ζcut εcut ζlimit εsample εvortex)
    (ε ξ aLoad η β:ℝ) (d:ℕ) (hε:0<ε) (hεvortex:ε≤εvortex)
    (haLoad:0<aLoad) (haLoad1:aLoad≤1) (hξEq:ξ=min (ε/200) (aLoad^2/160))
    (hη:0≤η) (hηcap:η≤δcut*(ρ₀/8)*ξ/1000) (hβ:0≤β) (hβ1:β≤1/4):
    ∃v₀:ℕ,1≤v₀ ∧
      OrdinaryActualTraceTriangleFineCoverAtLocalBalance buffer ρ₀ pmin href δcut ζcut εcut ζlimit εsample ε ξ aLoad κ β η d v₀ := by
  obtain ⟨v₀,hv₀,hcover⟩:=ordinary_vortex_supported_triangle_fine_cover_shared_numeric buffer hbuffer
    ρ₀ pmin href κ δcut ζcut εcut ζlimit εsample εvortex hρ₀ hδ hδsmall hnum
    ε ξ aLoad η β d hε hεvortex haLoad haLoad1 hξEq hη hηcap hβ hβ1
  refine ⟨v₀,hv₀,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P Gbase G Hbase Hs D vsize hGbase hreg hn hD hρlo hρhi hvsize
    Q π hπ σ coins j s Kres cost deepCost i hi A pR pH density εR εH Ledit βe βh αcut pstar θhost αhost
    f g I T B W ρi Ploc Floc Gloc Hloc localRaw localCoins R J S H S₀ H₀ X Tdeep Z Wdeep
    hpmin' hεRcap hεHcap hLcap hprofile hdensity hεR hεH hdegree hpEq hgood hnear htrace hstate hbal hdiv
    hDeep hRim hpH hpH1 hεcut0 hζcut0 hζlimit0 hLedit hδlim hhrefCap
  have hGP:G≤P := (ordinary_protected_trace_host_le S₀ G H₀ Hs X Tdeep Z Wdeep cost deepCost (i+1) A htrace hstate).trans (sdiff_le.trans hGbase)
  have hsupport:ordinaryHostResources G Hs⊆ordinaryRootResources (Q.extendedVertices (i+1)) (Q.extendedIndices (i+1)):=by
    rw [hstate]
    have hh:=ordinary_protected_trace_terminal S₀ H₀ X Tdeep Z Wdeep cost deepCost (i+1) (by omega) A htrace
    simpa only [X,Z,Nat.add_sub_cancel] using hh
  exact hcover V U Γ Color P G Hs D vsize hGP hreg hn hD hρlo hρhi hvsize Q π hπ σ coins j s (i+1) hi
    pR pH density εR εH Ledit βe βh αcut pstar θhost αhost hpmin' hεRcap hεHcap hLcap
    hprofile hεR hεH hnear hsupport hbal hdiv hDeep (by simpa [Nat.add_assoc] using hRim)
    hpH hpH1 hεcut0 hζcut0 hζlimit0 hLedit hδlim hhrefCap
end Oberwolfach
