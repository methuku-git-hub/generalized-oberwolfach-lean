module

public import Oberwolfach.OrdinaryFixedVortexCanonicalCleanupMargins
public import Oberwolfach.OrdinaryFixedVortexInitialCanonicalEdit
public import Oberwolfach.OrdinaryFixedVortexProfileFromPhysicalEdit
public import Oberwolfach.OrdinaryInitialCorrectedReservoirBalance

@[expose] public section
/-! On one raw sample, a bounded protected correction and decomposable
reserved absorber give the first-level cleanup profile, hub weights and
exactly balanced remaining host, with constants chosen before the host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_initial_corrected_sample_profile_early_vortex
    (mWheel d:ℕ) (ε ρ₀ α pmin η:ℝ) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀)
    (hα:0<α) (hpmin:0<pmin) (hη:0<η):
    ∃δ:ℝ,0<δ ∧ δ≤α ∧
    ∀(ζ δcap:ℝ),0<ζ→0≤δcap→δcap≤ζ/2→ζ≤δ→ζ≤δ*(ρ₀/8)→0<δcap→
    ∀ξlimit:ℝ,0<ξlimit→∃ξ:ℝ,0<ξ ∧ ξ≤ξlimit ∧
    ∀β:ℝ,0≤β→β≤1/4→β≤δ→∃v₀:ℕ,1≤v₀ ∧ ∀aK bK:ℕ,∃N:ℕ,1≤N ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→N≤Fintype.card V→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (j:Color) (σ:RawWheelOutcome V U Γ Color) (s:U→Color→ℝ)
      (pR pH θ εR εH βe βh b Bweight ηHub:ℝ),
      pmin≤pR→pR≤1→pmin≤pH→1/2≤θ→(θ+α)*Fintype.card V≤D→
      pR=initialIndexDensity U D*pH→(∀u,s u j=pH)→
      0≤εR→εR≤δ→0≤εH→εH≤δ→0≤βe→βe≤δ→0≤βh→βh≤δ→
    ∀(JQ:SimpleGraph V) (JH:V→U→Prop) (K:Finset (Sym2 V⊕(V×U))),
    let F:=permutationConflictGraph π (3*d);let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j;
    let Qcorr:=(R\F)\JQ;let Hcorr:=fun v u=>J v u∧¬JH v u;
    let G:=Qcorr\ordinaryResourceRim Qcorr K;let Hs:=fun v u=>Hcorr v u∧¬(Sum.inr (v,u)∈K);
    let f:=markedVortexVertexEmbedding Q 0;let g:=markedVortexHubEmbedding Q 0;
    let ρi:=markedVortexPermutation Q π hπ 0;let I:=markedVortexInnerVertices Q 0;let B:=markedVortexInnerHubs Q 0;
    let raw:=ordinaryRawRestrictPair f g σ;let L:=2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card;
    (∀v,(JQ.degree v:ℝ)+(Finset.univ.filter (JH v)).card≤10*ξ*Fintype.card V)→
    (∀u,((Finset.univ.filter (fun v=>JH v u)).card:ℝ)≤10*ξ*Fintype.card V)→
    (ordinaryResourceRows K).card≤aK→(ordinaryResourceHubs K).card≤bK→
    K⊆ordinaryHostResources Qcorr Hcorr→
    HasResourceDecomposition (ordinaryWheelResources (P:=R\F) (F:=F) (Hbase:=J) (r:=mWheel+1)) K→
    (∀v,Qcorr.degree v=2*(Finset.univ.filter (Hcorr v)).card)→
    (∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hcorr v u)).card)→
    OrdinaryFixedVortexRowIndexEvent 3 d εR εH P F D vsize β ε Q π hπ pR pH s j σ→
    OrdinaryAdaptiveHubWeightsLevelEvent mWheel (P.comap f) (F.comap f) I B ρi d pR pH (θ+α-β/2)
      (εR*I.card) (εH*B.card) L βe βh b Bweight ηHub (fun u=>s (g u)) j raw→
    G≤P ∧ Disjoint G F ∧
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card) ∧
    (∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hs v u)).card) ∧
    0≤L ∧ L≤ζ*I.card ∧
    OrdinaryCleanupParentProfiles (P.comap f) (G.comap f) (F.comap f) (fun v u=>Hs (f v) (g u)) ρi d I B
      pR pH (θ+α-β/2) (εR*I.card) (εH*B.card) L βe βh (fun u=>s (g u)) j raw ∧
    (∀v:I,|(((G.comap f).induce (I:Set _)).degree v:ℝ)-2*(Finset.univ.filter (fun u:B=>Hs (f v.val) (g u.val))).card|≤η*I.card) ∧
    Nonempty (OrdinaryMixedHubWeightsOfLength mWheel b Bweight ηHub (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) I B):=by
  obtain ⟨δ,hδ,hδα,hmargin⟩:=ordinary_fixed_vortex_canonical_cleanup_margins ε ρ₀ α pmin pmin η d
    hε hε1 hρ₀ hα hpmin hpmin hη
  refine ⟨δ,hδ,hδα,?_⟩
  intro ζ δcap hζ hδcap0 hδcapζ hζδ hζB hδcap ξlimit hξlimit
  obtain ⟨ξ,hξ,hξlim,hedit⟩:=ordinary_fixed_vortex_initial_canonical_edit ε ρ₀ δcap ξlimit hε hρ₀ hδcap hξlimit
  refine ⟨ξ,hξ,hξlim,?_⟩
  intro β hβ hβ1 hβδ
  obtain ⟨v₀,hv₀,hmargin⟩:=hmargin ζ δcap hζ hδcap0 hδcapζ hζδ hζB β hβ hβ1 hβδ
  refine ⟨v₀,hv₀,?_⟩
  intro aK bK
  obtain ⟨N,hN,hedit⟩:=hedit d aK bK
  refine ⟨N,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hD hρlo hρhi hv hnN Q π hπ j σ s
    pR pH θ εR εH βe βh b Bweight ηHub hpR hpR1 hpH hθ hdegree hpEq hs hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh JQ JH K
    F R J Qcorr Hcorr G Hs f g ρi I B raw L hrow hcol hrows hhubs hK hdec hbal hdiv hgood hevent
  have hvsize:0<vsize:=by omega
  have hpR0:0≤pR:=hpmin.le.trans hpR
  have hpH0:0≤pH:=hpmin.le.trans hpH
  have hρ:0< initialIndexDensity U D:=hρ₀.trans_le hρlo
  have hbase:=ordinary_initial_corrected_reservoir_balance P F JQ (R\F) F JH J π d (mWheel+1) j σ K hK hdec hbal hdiv
  have hphys:=hedit V U Γ Color P D vsize β hreg hn hD hρlo hρhi hβ hβ1 hvsize hnN Q π hπ j σ JQ JH K hrow hcol hrows hhubs hK
  have hmarg:=hmargin V U P D vsize hreg hn hD hρlo hρhi hv Q 0 Q.length_pos
    pR pH θ εR εH βe βh hpR hpR1 hpH hθ hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh
  have hGP:(G.comap f)≤(P.comap f):=by intro v w hvw;exact hbase.1 hvw
  have hdis:Disjoint (G.comap f) (F.comap f):=by
    apply disjoint_iff_inf_le.mpr
    intro v w hvw
    exact (disjoint_iff_inf_le.mp hbase.2.1) ⟨hvw.1,hvw.2⟩
  have hnearMargin:(initialIndexDensity U D*pH)*β*I.card+εR*I.card+2*(εH*B.card)+3*L≤η*I.card:=by
    rw [←hpEq]
    exact hmarg.2.2.2.2.2.2
  have hh:=ordinary_fixed_vortex_profile_from_physical_edit mWheel P F D vsize β ε θ α pR pH εR εH L βe βh η b Bweight ηHub
    Q π hπ d s j σ hn hreg hρ hβ hpR0 hpR1 hpH0 hεR0 hεH0 hmarg.1 hθ (by linarith) hdegree hpEq hs hgood 0 Q.length_pos
    (G.comap f) (fun v u=>Hs (f v) (g u)) hGP hdis hphys hmarg.2.2.2.2.1 hmarg.2.2.2.2.2.1 hnearMargin hevent
  refine ⟨hbase.1,hbase.2.1,hbase.2.2.2.1,hbase.2.2.2.2,hmarg.1,hmarg.2.1,hh.1,?_,?_⟩
  · convert hh.2.1 using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · convert hh.2.2 using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
