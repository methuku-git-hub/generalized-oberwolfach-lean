module

public import Oberwolfach.OrdinaryNonrootCoverNumericInputsExplicit
public import Oberwolfach.OrdinaryVortexSupportedLocalExactBalance
public import Oberwolfach.OrdinaryProtectedTraceInvariant
public import Oberwolfach.OrdinaryVortexBufferedDomains
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

theorem ordinary_vortex_deep_trace_nonroot_cover_from_local_balance_explicit
    (mWheel K buffer:ℕ) (hbuffer:2≤buffer) (hm:3≤mWheel) (ρ₀ ε δcut ξ:ℝ)
    (hρ₀:0<ρ₀) (hε:0<ε) (hδ:0<δcut) (hδsmall:δcut<1/4) (hξ:0<ξ) (hξε:ξ≤ε/100):
    ∃η₀:ℝ,η₀=δcut*(ρ₀/8)*ξ/1000 ∧ 0<η₀ ∧ ∃n₀:ℕ,∀η:ℝ,0≤η→η≤η₀→
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U],
    ∀(P JQ G:SimpleGraph V) (JH Hs:V→U→Prop) (D vsize:ℕ) (β:ℝ),
      P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→0≤β→β≤1/4→0<vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (σ:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool) (d:ℕ) (j:Color) (s:U→Color→ℝ)
      (Kres:Finset (Sym2 V⊕(V×U))) (cost deepCost:ℕ→ℝ) (i:ℕ),i+1<Q.length→
    ∀(A:Finset (Sym2 V⊕(V×U))) (a aLoad ρ θ ζlimit pR pH density εR εH Ledit βe βh ζcut εcut href αcut pstar θhost αhost:ℝ),
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
    OrdinaryNonrootNumericInputs Floc I T B W n₀ d (ρ₀/8) a ρ θ aLoad ζlimit ε δcut ζcut εcut pH εR εH Ledit href→
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
    0<aLoad→aLoad≤1→80*ξ≤aLoad^2→
    OrdinaryNonrootWheelCoverResult mWheel K ξ aLoad Gloc Floc Hloc I T B W :=by
  obtain ⟨η₀,hηEq,hη₀,n₀,hmain⟩:=ordinary_nonroot_cover_from_numeric_inputs_explicit mWheel K hm (ρ₀/8) ε δcut ξ
    (by positivity) hε hδ hδsmall hξ hξε
  refine ⟨η₀,hηEq,hη₀,n₀,?_⟩
  intro η hη hη0 V U Γ Color _ _ _ _ _ _ P JQ G JH Hs D vsize β hreg hn hD hρlo hρhi hβ hβ1 hvsize
    Q π hπ σ coins d j s Kres cost deepCost i hi A a aLoad ρ θ ζlimit pR pH density εR εH Ledit βe βh ζcut εcut href αcut pstar θhost αhost
    f g I T B W ρi Ploc Floc Gloc Hloc localRaw localCoins R J S H S₀ H₀ X Tdeep Z Wdeep
    hnums hprofile hdensity hεR hεH hdegree hpEq hgood hnear htrace hstate hbal hdiv hDeep hRim hpH hpH1 hεcut hζcut hζlimit hLedit hδlim hhref haLoad haLoad1 hξsmall
  have hQ0:S₀≤P:=by
    exact (show S₀≤S from sdiff_le).trans ((show S≤R from sdiff_le.trans sdiff_le).trans (retainedGraph_le P _))
  have hGP:G≤P:=(ordinary_protected_trace_host_le S₀ G H₀ Hs X Tdeep Z Wdeep cost deepCost (i+1) A htrace hstate).trans hQ0
  have hGloc:Gloc≤Ploc:=by intro v w hvw;exact hGP hvw
  have hsupport:ordinaryHostResources G Hs⊆ordinaryRootResources (Q.extendedVertices (i+1)) (Q.extendedIndices (i+1)):=by
    rw [hstate]
    have hh:=ordinary_protected_trace_terminal S₀ H₀ X Tdeep Z Wdeep cost deepCost (i+1) (by omega) A htrace
    simpa only [X,Z,Nat.add_sub_cancel] using hh
  have hExact:=ordinary_vortex_supported_local_exact_balance P G Hs D vsize β ε Q (mWheel+1) (i+1) hsupport hbal hdiv
  have hU:Fintype.card (markedVortexHubType Q (i+1))≤Fintype.card (markedVortexVertexType Q (i+1)):=
    (marked_vortex_fixed_ambient_size_fields Q hreg hn hD hρ₀ hρlo hρhi hβ hβ1 hε hvsize (i+1) hi).2.2
  have hFcut:∀v,Floc.degree v≤2*(3*d):=by
    intro v
    exact ordinary_fixed_vortex_conflict_degree P D vsize β ε Q π hπ (i+1) (3*d) v
  have hRimLocal:=ordinary_fixed_vortex_rim_cut_transport P D vsize β ε Q σ coins (i+1) αcut pstar (by simpa [Nat.add_assoc] using hRim)
  have hDeeplocal:=hDeep (i+1) hi
  have hQbalLocal:∀v∈T,Gloc.degree v=2*(Finset.univ.filter (Hloc v)).card:=by
    intro v hv
    exact hExact.1 v
  have hHdivLocal:∀u∈W,(mWheel+1)∣(Finset.univ.filter (fun v=>Hloc v u)).card:=by
    intro u hu
    exact hExact.2 u
  have hout:=hmain η hη hη0 (markedVortexVertexType Q (i+1)) (markedVortexHubType Q (i+1)) Γ Color
    Gloc Ploc Floc Hloc I T B W ρi d j localRaw localCoins a aLoad ρ θ ζlimit pR pH density εR εH Ledit βe βh ζcut εcut href αcut pstar
    (fun u=>s (g u)) (by convert hprofile using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hnums hpH hpH1 hεcut hζcut hζlimit hLedit hδlim hhref hRimLocal hFcut hnear (by convert hDeeplocal using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) haLoad haLoad1 hξsmall hU hGloc hQbalLocal hHdivLocal
  exact hout
end Oberwolfach
