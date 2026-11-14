module

public import Oberwolfach.OrdinaryVortexBufferedDomains
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

theorem ordinary_vortex_initial_buffered_nonroot_cover
    (mWheel K buffer:ℕ) (hm:3≤mWheel) (ρ₀ ε δcut ξ:ℝ)
    (hρ₀:0<ρ₀) (hε:0<ε) (hδ:0<δcut) (hδsmall:δcut<1/4) (hξ:0<ξ) (hξε:ξ≤ε/100):
    ∃η₀:ℝ,0<η₀ ∧ ∃n₀:ℕ,∀η:ℝ,0≤η→η≤η₀→
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U],
    ∀(P G:SimpleGraph V) (Hs:V→U→Prop) (D vsize:ℕ) (β:ℝ),
      P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→0≤β→β≤1/4→0<vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (σ:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool) (d:ℕ) (j:Color) (s:U→Color→ℝ),
    ∀(a aLoad ρ θ ζlimit pR pH density εR εH Ledit βe βh ζcut εcut href αcut pstar:ℝ),
    let f:markedVortexVertexType Q 0↪V:=(markedVortexVertexEmbedding Q 0).toEmbedding;
    let g:=markedVortexHubEmbedding Q 0;let I:=markedVortexInnerVertices Q 0;let T:=ordinaryVortexBufferedVertices Q 0 buffer;
    let B:=markedVortexInnerHubs Q 0;let W:=ordinaryVortexBufferedHubs Q 0 buffer;
    let ρi:=markedVortexPermutation Q π hπ 0;
    let Ploc:=P.comap f;let Floc:=(permutationConflictGraph π (3*d)).comap f;
    let Gloc:=G.comap f;let Hloc:=fun v u=>Hs (f v) (g u);
    let localRaw:=ordinaryRawRestrictPair f g σ;
    let localCoins:=fun e:Sym2 (markedVortexVertexType Q 0)=>coins (Sym2.map f e);
    OrdinaryNonrootNumericInputs Floc I T B W n₀ d (ρ₀/8) a ρ θ aLoad ζlimit ε δcut ζcut εcut pH εR εH Ledit href→
    OrdinaryCleanupParentProfiles Ploc Gloc Floc Hloc ρi d I B pR pH density (εR*I.card) (εH*B.card) Ledit βe βh (fun u=>s (g u)) j localRaw→
    (∀v:I,|(((Gloc.induce (I:Set _)).degree v):ℝ)-2*(Finset.univ.filter (fun u:B=>Hloc v.val u.val)).card|≤η*I.card)→
    G≤P→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→(∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    OrdinaryFixedVortexDeepCoverEvent mWheel K d a aLoad ρ θ P D vsize β ε Q π hπ j σ→
    OrdinaryInducedRimCutEvent (Q.extendedVertices 1) (sampledOrientation (rawWheelGraph P σ) coins) αcut pstar→
    0<pH→pH≤1→0≤εcut→0≤ζcut→0≤ζlimit→0≤Ledit→
    δcut≤min (αcut/32) (pstar/512)→href≤αcut*pstar/64→
    0<aLoad→aLoad≤1→80*ξ≤aLoad^2→
    OrdinaryNonrootWheelCoverResult mWheel K ξ aLoad Gloc Floc Hloc I T B W :=by
  obtain ⟨η₀,hη₀,n₀,hmain⟩:=ordinary_nonroot_cover_from_numeric_inputs mWheel K hm (ρ₀/8) ε δcut ξ
    (by positivity) hε hδ hδsmall hξ hξε
  refine ⟨η₀,hη₀,n₀,?_⟩
  intro η hη hη0 V U Γ Color _ _ _ _ _ _ P G Hs D vsize β hreg hn hD hρlo hρhi hβ hβ1 hvsize
    Q π hπ σ coins d j s a aLoad ρ θ ζlimit pR pH density εR εH Ledit βe βh ζcut εcut href αcut pstar
    f g I T B W ρi Ploc Floc Gloc Hloc localRaw localCoins
    hnums hprofile hnear hGP hbal hdiv hDeep hRim hpH hpH1 hεcut hζcut hζlimit hLedit hδlim hhref haLoad haLoad1 hξsmall
  have hsupport:ordinaryHostResources G Hs⊆ordinaryRootResources (Q.extendedVertices 0) (Q.extendedIndices 0):=by
    apply ordinaryRootResources_contains
    · intro v hv
      rw [Q.extendedVertices_eq (Nat.zero_le _),Q.initial]
      exact Finset.mem_univ v
    · intro u hu
      rw [Q.extendedIndices_eq (Nat.zero_le _),Q.indices_initial]
      exact Finset.mem_univ u
  have hGloc:Gloc≤Ploc:=by intro v w hvw;exact hGP hvw
  have hExact:=ordinary_vortex_supported_local_exact_balance P G Hs D vsize β ε Q (mWheel+1) 0 hsupport hbal hdiv
  have hU:Fintype.card (markedVortexHubType Q 0)≤Fintype.card (markedVortexVertexType Q 0):=
    (marked_vortex_fixed_ambient_size_fields Q hreg hn hD hρ₀ hρlo hρhi hβ hβ1 hε hvsize 0 Q.length_pos).2.2
  have hFcut:∀v,Floc.degree v≤2*(3*d):=by
    intro v
    exact ordinary_fixed_vortex_conflict_degree P D vsize β ε Q π hπ 0 (3*d) v
  have hRimLocal:=ordinary_fixed_vortex_rim_cut_transport P D vsize β ε Q σ coins 0 αcut pstar hRim
  have hDeeplocal:=hDeep 0 Q.length_pos
  have hQbalLocal:∀v∈T,Gloc.degree v=2*(Finset.univ.filter (Hloc v)).card:=by
    intro v hv
    exact hExact.1 v
  have hHdivLocal:∀u∈W,(mWheel+1)∣(Finset.univ.filter (fun v=>Hloc v u)).card:=by
    intro u hu
    exact hExact.2 u
  have hout:=hmain η hη hη0 (markedVortexVertexType Q 0) (markedVortexHubType Q 0) Γ Color
    Gloc Ploc Floc Hloc I T B W ρi d j localRaw localCoins a aLoad ρ θ ζlimit pR pH density εR εH Ledit βe βh ζcut εcut href αcut pstar
    (fun u=>s (g u)) (by convert hprofile using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hnums hpH hpH1 hεcut hζcut hζlimit hLedit hδlim hhref hRimLocal hFcut hnear
    (by convert hDeeplocal using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) haLoad haLoad1 hξsmall hU hGloc hQbalLocal hHdivLocal
  exact hout
end Oberwolfach
