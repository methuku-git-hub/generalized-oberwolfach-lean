module

public import Oberwolfach.OrdinaryFixedVortexInitialPhysicalEdit
public import Oberwolfach.OrdinaryFixedVortexInitialEditBudget
public import Oberwolfach.PermutationConflictDegree

@[expose] public section
/-! Choose the initial correction rate before the host, while allowing the
finite reservoir size to be fixed later. The resulting actual edit fits the
same canonical cap used by the common adaptive hub event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fixed_vortex_initial_canonical_edit
    (ε ρ₀ δcap ξlimit:ℝ) (hε:0<ε) (hρ₀:0<ρ₀) (hδcap:0<δcap) (hξlimit:0<ξlimit):
    ∃ξ:ℝ,0<ξ ∧ ξ≤ξlimit ∧ ∀d aK bK:ℕ,∃N:ℕ,1≤N ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D vsize:ℕ) (β:ℝ),
      P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→0≤β→β≤1/4→0<vsize→N≤Fintype.card V→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (j:Color) (σ:RawWheelOutcome V U Γ Color)
      (JQ:SimpleGraph V) (JH:V→U→Prop) (K:Finset (Sym2 V⊕(V×U))),
    (∀v,(JQ.degree v:ℝ)+(Finset.univ.filter (JH v)).card≤10*ξ*Fintype.card V)→
    (∀u,((Finset.univ.filter (fun v=>JH v u)).card:ℝ)≤10*ξ*Fintype.card V)→
    (ordinaryResourceRows K).card≤aK→(ordinaryResourceHubs K).card≤bK→
    K⊆ordinaryHostResources (((rawWheelGraph P σ)\(permutationConflictGraph π (3*d)))\JQ)
      (fun v u=>rawWheelSpokes π d σ j v u∧¬JH v u)→
    let f:markedVortexVertexType Q 0↪V:=(markedVortexVertexEmbedding Q 0).toEmbedding;
    let g:=markedVortexHubEmbedding Q 0;let ρ:=markedVortexPermutation Q π hπ 0;
    let I:=markedVortexInnerVertices Q 0;let B:=markedVortexInnerHubs Q 0;
    let raw:=ordinaryRawRestrictPair f g σ;
    let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j;
    let Qcorr:=(R\(permutationConflictGraph π (3*d)))\JQ;let Hcorr:=fun v u=>J v u∧¬JH v u;
    let G:=Qcorr\ordinaryResourceRim Qcorr K;let Hs:=fun v u=>Hcorr v u∧¬(Sum.inr (v,u)∈K);
    let Ledit:=2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card;
    ∀w:markedVortexVertexType Q 0⊕markedVortexHubType Q 0,
      ((changed ((ordinaryPhysicalGraph (rawWheelGraph (P.comap f) raw) (rawWheelSpokes ρ d raw j)).neighborFinset w)
        ((ordinaryPhysicalGraph (G.comap f) (fun v u=>Hs (f v) (g u))).neighborFinset w)).card:ℝ)≤Ledit:=by
  obtain ⟨ξ₀,hξ₀,hmain⟩:=ordinary_fixed_vortex_initial_edit_budget ε ρ₀ δcap hε hρ₀ hδcap
  let ξ:=min ξ₀ ξlimit
  have hξ:0<ξ:=lt_min hξ₀ hξlimit
  have hξ₀':ξ≤ξ₀:=min_le_left _ _
  refine ⟨ξ,hξ,min_le_right _ _,?_⟩
  intro d aK bK
  let C:ℝ:=2*((3*d:ℕ):ℝ)+aK+bK
  have hC:0≤C:=by dsimp [C];positivity
  obtain ⟨N,hN,hbudget⟩:=hmain C hC
  refine ⟨N,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize β hreg hn hD hρlo hρhi hβ hβ1 hvsize hnN Q π hπ j σ JQ JH K
    hrow hcol hrows hhubs hK f g ρ I B raw R J Qcorr Hcorr G Hs Ledit w
  have hn0:(0:ℝ)≤Fintype.card V:=by positivity
  have hscale:10*ξ*(Fintype.card V:ℝ)≤10*ξ₀*Fintype.card V:=by
    have hh:=mul_le_mul_of_nonneg_right hξ₀' hn0
    nlinarith only [hh]
  have hrow':∀v,(JQ.degree v:ℝ)+(Finset.univ.filter (JH v)).card≤10*ξ₀*Fintype.card V:=fun v=>(hrow v).trans hscale
  have hcol':∀u,((Finset.univ.filter (fun v=>JH v u)).card:ℝ)≤10*ξ₀*Fintype.card V:=fun u=>(hcol u).trans hscale
  have hcost:=hbudget V U P D vsize β hreg hn hD hρlo hρhi hβ hβ1 hvsize hnN Q
  have hcostmin:10*ξ₀*(Fintype.card V:ℝ)+C≤δcap*min (I.card:ℝ) B.card:=by
    rcases le_total (I.card:ℝ) B.card with hh | hh
    · rw [min_eq_left hh]
      exact hcost.2.1
    · rw [min_eq_right hh]
      exact hcost.2.2
  have hrowK:((ordinaryResourceRows K).card:ℝ)≤aK:=by exact_mod_cast hrows
  have hhubK:((ordinaryResourceHubs K).card:ℝ)≤bK:=by exact_mod_cast hhubs
  have hbudget':2*((3*d:ℕ):ℝ)+10*ξ₀*(Fintype.card V:ℝ)+(ordinaryResourceRows K).card+(ordinaryResourceHubs K).card≤Ledit:=by
    have hnon:(0:ℝ)≤2*((3*d:ℕ):ℝ):=by positivity
    dsimp [C,Ledit] at *
    linarith only [hcostmin,hrowK,hhubK,hnon]
  have hF:∀v,((permutationConflictGraph π (3*d)).degree v:ℝ)≤2*((3*d:ℕ):ℝ):=by
    intro v
    have hh:=permutationConflictGraph_degree_le π (3*d) v
    exact_mod_cast hh
  have he:=ordinary_fixed_vortex_initial_physical_edit P (permutationConflictGraph π (3*d)) JQ JH D vsize β ε Q π hπ d j σ K
    (2*((3*d:ℕ):ℝ)) (10*ξ₀*Fintype.card V) Ledit (by positivity) hF hrow' hcol' hK hbudget'
  exact he w
end Oberwolfach
