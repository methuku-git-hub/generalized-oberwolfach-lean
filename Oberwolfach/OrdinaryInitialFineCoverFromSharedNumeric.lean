module

public import Oberwolfach.OrdinaryVortexInitialBufferedFineCover
public import Oberwolfach.OrdinaryInitialNumericFromShared

@[expose] public section
/-! The shared before-spacing numeric choices provide the initial fine
cover for any balanced edited host with the sampled profile and tests. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 35000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_initial_fine_cover_from_shared_numeric
    (mWheel loadK d:ℕ) (hm:3≤mWheel)
    (ρ₀ pmin href a ρ θ δcut ζcut εcut ζlimit εsample εvortex ε ξroot aLoad ηbal αcut pstar:ℝ)
    (hnum:OrdinaryFixedVortexNonrootNumericAt ρ₀ pmin href a ρ θ δcut ζcut εcut ζlimit εsample εvortex)
    (hρ₀:0<ρ₀) (hε:0<ε) (hεv:ε≤εvortex) (hδ:0<δcut) (hδsmall:δcut<1/4)
    (hξ:0<ξroot) (hξε:ξroot≤ε/100) (ha:0<aLoad) (ha1:aLoad≤1) (hξsmall:80*ξroot≤aLoad^2)
    (hbal:0≤ηbal) (hbalcap:ηbal≤δcut*(ρ₀/8)*ξroot/1000)
    (hζcut:0≤ζcut) (hεcut:0≤εcut) (hζlimit:0≤ζlimit)
    (hδlim:δcut≤min (αcut/32) (pstar/512)) (hhref:href≤αcut*pstar/64):
    ∀β:ℝ,0≤β→β≤1/4→∃v₀:ℕ,1≤v₀ ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder U],
    ∀(P G:SimpleGraph V) (Hs:V→U→Prop) (D mv:ℕ),
      P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤mv→
    ∀(Q:Vortex U P D β ε mv) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (σ:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool) (j:Color) (sp:U→Color→ℝ)
      (pR pH density εR εH Ledit βe βh:ℝ),
    let f:=markedVortexVertexEmbedding Q 0;let g:=markedVortexHubEmbedding Q 0;
    let I:=markedVortexInnerVertices Q 0;let T:=ordinaryVortexBufferedVertices Q 0 2;
    let B:=markedVortexInnerHubs Q 0;let W:=ordinaryVortexBufferedHubs Q 0 2;
    let ρi:=markedVortexPermutation Q π hπ 0;
    let Ploc:=P.comap f;let Floc:=(permutationConflictGraph π (3*d)).comap f;
    let Gloc:=G.comap f;let Hloc:=fun v u=>Hs (f v) (g u);
    let raw:=ordinaryRawRestrictPair f g σ;
    pmin≤pH→pH≤1→0<pH→0≤εR→εR≤εsample→0≤εH→εH≤εsample→0≤Ledit→Ledit≤ζlimit*I.card→
    OrdinaryCleanupParentProfiles Ploc Gloc Floc Hloc ρi d I B pR pH density
      (εR*I.card) (εH*B.card) Ledit βe βh (fun u=>sp (g u)) j raw→
    (∀v:I,|((Gloc.induce (I:Set _)).degree v:ℝ)-2*(Finset.univ.filter (fun u:B=>Hloc v.val u.val)).card|≤ηbal*I.card)→
    G≤P→(∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
      (∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    OrdinaryFixedVortexDeepCoverEvent mWheel loadK d a aLoad ρ θ P D mv β ε Q π hπ j σ→
    OrdinaryInducedRimCutEvent (Q.extendedVertices 1) (sampledOrientation (rawWheelGraph P σ) coins) αcut pstar→
    OrdinaryFineWheelCoverResult mWheel loadK ξroot aLoad Gloc Floc Hloc I T B W :=by
  obtain ⟨η₀,hηeq,hη₀,n₀,hcover⟩:=ordinary_vortex_initial_buffered_fine_cover mWheel loadK 2 hm ρ₀ ε δcut ξroot
    hρ₀ hε hδ hδsmall hξ hξε
  have hηcap:ηbal≤η₀:=by rw [hηeq]; exact hbalcap
  intro β hβ hβ1
  obtain ⟨v₀,hv₀,hnum⟩:=ordinary_initial_numeric_from_shared ρ₀ pmin href a ρ θ δcut ζcut εcut ζlimit εsample εvortex
    hnum ε hε hεv aLoad ha β hβ hβ1 d n₀
  refine ⟨v₀,hv₀,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P G Hs D mv hreg hn hD hρlo hρhi hmv Q π hπ σ coins j sp
    pR pH density εR εH Ledit βe βh f g I T B W ρi Ploc Floc Gloc Hloc raw
    hpH hpH1 hpHpos hεR hεRcap hεH hεHcap hL hLcap hprofile hnear hGP hGbal hGdiv hDeep hRim
  have hnums:=hnum V U P D mv hreg hn hD hρlo hρhi hmv Q π hπ pH εR εH Ledit
    hpH hεR hεRcap hεH hεHcap hL hLcap
  have hh:=hcover ηbal hbal hηcap V U Γ Color P G Hs D mv β hreg hn hD hρlo hρhi hβ hβ1 (by omega)
    Q π hπ σ coins d j sp a aLoad ρ θ ζlimit pR pH density εR εH Ledit βe βh ζcut εcut href αcut pstar
    hnums hprofile hnear hGP hGbal hGdiv hDeep hRim hpHpos hpH1 hεcut hζcut hζlimit hL hδlim hhref ha ha1 hξsmall
  convert hh using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
end Oberwolfach
