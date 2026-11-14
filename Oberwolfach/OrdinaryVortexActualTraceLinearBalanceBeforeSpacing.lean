module

public import Oberwolfach.OrdinaryVortexCleanupSeparatedLinearBoundaryMarginsBeforeSpacing
public import Oberwolfach.OrdinaryVortexTraceProfileProtectedPair
public import Oberwolfach.OrdinaryFixedVortexCleanupBalance
public import Oberwolfach.OrdinaryVortexCleanupUniformOriginalMargins

@[expose] public section
/-! Choose cleanup tolerances before the vortex and obtain the profile and
balance on each actual protected trace, with the numerical margins supplied
by the vortex geometry and the latest-loss bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_actual_trace_separated_linear_balance_before_spacing
    (ρ₀ α pmin hmin:ℝ) (hρ₀:0<ρ₀)
    (hα:0<α) (hpmin:0<pmin) (hhmin:0<hmin):
    ∃cBoundary:ℝ,0<cBoundary ∧ ∀ε:ℝ,0<ε→ε<1/4→∀η:ℝ,0<η→
    ∃δ:ℝ,0<δ ∧ δ≤α ∧ ∀(d:ℕ),∀β:ℝ,0≤β→β≤1/4→β≤δ→
    ∃m₀:ℕ,1≤m₀ ∧ ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(P Gbase:SimpleGraph V) (Hbase:V→U→Prop) (D m:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→
    ∀(Q:Vortex U P D β ε m) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
      (pR pH θ εR εH βe βh:ℝ),pmin≤pR→pR≤1→hmin≤pH→1/2≤θ→(θ+α)*Fintype.card V≤D→
      pR=initialIndexDensity U D*pH→(∀u,s u j=pH)→
      0≤εR→εR≤δ→0≤εH→εH≤δ→0≤βe→βe≤cBoundary*ε→0≤βh→βh≤cBoundary*ε→
    ∀(K:Finset (Sym2 V⊕(V×U))),
      (∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,
        ((rawWheelGraph P σ)\permutationConflictGraph π (3*d)).Adj v w↔Gbase.Adj v w)→
      (∀v∈Q.extendedVertices 1,∀u∈Q.extendedIndices 1,
        rawWheelSpokes π d σ j v u↔Hbase v u)→
      Disjoint K (ordinaryRootResources (Q.extendedVertices 1) (Q.extendedIndices 1))→
      OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d))
        D m β ε Q π hπ pR pH s j σ→
    ∀(cost deepCost:ℕ→ℝ) (i buffer:ℕ),2≤buffer→i+1<Q.length→
    ∀(A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop),
    let F:=permutationConflictGraph π (3*d);
    let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j;
    let S:=Gbase;let H:=Hbase;
    let S₀:=S\ordinaryResourceRim S K;let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K);
    let X:=fun k=>Q.extendedVertices (k+1);let T:=fun k=>Q.extendedVertices (k+buffer);
    let Z:=fun k=>Q.extendedIndices (k+1);let W:=fun k=>Q.extendedIndices (k+buffer);
    let I:=markedVortexInnerVertices Q (i+1);let B:=markedVortexInnerHubs Q (i+1);
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1);
    let ρ:=markedVortexPermutation Q π hπ (i+1);
    let Jwin:=Finset.Icc (i+2-buffer) i;
    OrdinaryProtectedTrace S₀ H₀ X T Z W cost deepCost (i+1) A→
    ordinaryHostResources G Hs=A→0≤(∑j∈Jwin,cost j)→(∑j∈Jwin,cost j)≤δ*I.card→(∑j∈Jwin,cost j)≤δ*B.card→
    OrdinaryCleanupParentProfiles (P.comap f) (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) ρ d I B pR pH (θ+α-β/2)
      (εR*I.card) (εH*B.card) (2*((3*d:ℕ):ℝ)+(∑j∈Jwin,cost j)) βe βh (fun u=>s (g u)) j
      (ordinaryRawRestrictPair f g σ) ∧
    (∀v:I,|(((G.comap f).induce (I:Set _)).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:B=>Hs (f v.val) (g u.val))).card|≤η*I.card) ∧
    (initialIndexDensity U D*pH)*β*I.card+εR*I.card+2*(εH*B.card)+
      3*(2*((3*d:ℕ):ℝ)+(∑j∈Jwin,cost j))≤η*I.card:=by
  obtain ⟨cBoundary,hcBoundary,hmain⟩:=ordinary_vortex_cleanup_separated_linear_boundary_margins_before_spacing ρ₀ α pmin hmin
    hρ₀ hα hpmin hhmin
  refine ⟨cBoundary,hcBoundary,?_⟩
  intro ε hε hε1 η hη
  obtain ⟨δ,hδ,hδα,hmain⟩:=hmain ε hε hε1 η hη
  refine ⟨δ,hδ,hδα,?_⟩
  intro d β hβ0 hβ1 hβ
  obtain ⟨m₀,hm₀,hmargin⟩:=hmain (3*d) β hβ0 hβ1 hβ
  refine ⟨m₀,hm₀,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P Gbase Hbase D m hreg hn hD hρlo hρhi hm Q π hπ s j σ
    pR pH θ εR εH βe βh hpRlo hpR1 hpHlo hθ hdegree hpEq hs hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh K hPairRim hPairSpoke havoid hgood
    cost deepCost i buffer hbuffer hi A G Hs F R J S H S₀ H₀ X T Z W I B f g ρ Jwin htrace hstate hcost hcostI hcostB
  have hρ:0< initialIndexDensity U D:=lt_of_lt_of_le hρ₀ hρlo
  have hpR:0<pR:=lt_of_lt_of_le hpmin hpRlo
  have hpH:0<pH:=lt_of_lt_of_le hhmin hpHlo
  have hdensity:1/2≤θ+α-β/2:=by linarith
  have hnum:=hmargin V U P D m hreg hn hD hρlo hρhi hm Q (i+1) hi
    pR pH θ εR εH βe βh ((∑j∈Jwin,cost j)) hpRlo hpR1 hpHlo hθ hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh hcost hcostI hcostB
  have hbal:=hnum.2.2
  rw [hpEq] at hbal
  have hF:∀v,((permutationConflictGraph π (3*d)).degree v:ℝ)≤2*((3*d:ℕ):ℝ):=by
    intro v
    exact_mod_cast permutationConflictGraph_degree_le π (3*d) v
  have hprofile:=ordinary_vortex_trace_buffered_profile_protected_pair P Gbase F Hbase D m β ε θ α pR pH εR εH
    Q π hπ d s j σ K (Q.extendedVertices 1) (Q.extendedIndices 1) (by rfl) (by rfl)
    hPairRim hPairSpoke havoid (2*((3*d:ℕ):ℝ)) (by positivity) hF
    hn hreg hρ hβ0 hpR.le hpR1 hpH.le hdensity hdegree hs hgood cost deepCost i buffer hbuffer hi A G Hs βe βh
    htrace hstate hnum.1 hnum.2.1
  have hL:0≤2*((3*d:ℕ):ℝ)+∑j∈Jwin,cost j:=by positivity
  have hnear:=ordinary_fixed_vortex_cleanup_balance P F D m β ε θ α pR pH εR εH
    (2*((3*d:ℕ):ℝ)+∑j∈Jwin,cost j) βe βh η Q π hπ d s j σ hn hreg hρ hβ0 hpH.le hεR0 hεH0 hL hdegree hpEq hgood
    (i+1) hi (G.comap f) (fun v u=>Hs (f v) (g u))
    (by convert hprofile using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _) hbal
  exact ⟨hprofile,by convert hnear using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _,hbal⟩
end Oberwolfach
