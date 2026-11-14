module

public import Oberwolfach.OrdinaryInitialCorrectionReservoirEdit
public import Oberwolfach.OrdinaryInducedPhysicalEditOfGlobal
public import Oberwolfach.OrdinaryRawPairStateEquality
public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! Restrict the initial correction and reservoir edit to the actual first
vortex parent, on the same raw sample and local permutation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_fixed_vortex_initial_physical_edit
    (P F JQ:SimpleGraph V) (JH:V→U→Prop) (D vsize:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (j:Color) (σ:RawWheelOutcome V U Γ Color) (K:Finset (Sym2 V⊕(V×U)))
    (Lconf Lcorr Ledit:ℝ) (hLconf:0≤Lconf) (hF:∀v,(F.degree v:ℝ)≤Lconf)
    (hrow:∀v,(JQ.degree v:ℝ)+(Finset.univ.filter (JH v)).card≤Lcorr)
    (hcol:∀u,((Finset.univ.filter (fun v=>JH v u)).card:ℝ)≤Lcorr)
    (hK:K⊆ordinaryHostResources (((rawWheelGraph P σ)\F)\JQ)
      (fun v u=>rawWheelSpokes π d σ j v u∧¬JH v u))
    (hbudget:Lconf+Lcorr+(ordinaryResourceRows K).card+(ordinaryResourceHubs K).card≤Ledit):
    let f:markedVortexVertexType Q 0↪V:=(markedVortexVertexEmbedding Q 0).toEmbedding;
    let g:=markedVortexHubEmbedding Q 0;let ρ:=markedVortexPermutation Q π hπ 0;
    let raw:=ordinaryRawRestrictPair f g σ;
    let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j;
    let Qcorr:=(R\F)\JQ;let Hcorr:=fun v u=>J v u∧¬JH v u;
    let G:=Qcorr\ordinaryResourceRim Qcorr K;let Hs:=fun v u=>Hcorr v u∧¬(Sum.inr (v,u)∈K);
    ∀w:markedVortexVertexType Q 0⊕markedVortexHubType Q 0,
      ((changed ((ordinaryPhysicalGraph (rawWheelGraph (P.comap f) raw) (rawWheelSpokes ρ d raw j)).neighborFinset w)
        ((ordinaryPhysicalGraph (G.comap f) (fun v u=>Hs (f v) (g u))).neighborFinset w)).card:ℝ)≤Ledit:=by
  intro f g ρ raw R J Qcorr Hcorr G Hs
  have hglobal:=ordinary_initial_correction_reservoir_physical_edit R F JQ J JH K Lconf Lcorr hLconf hF hrow hcol hK
  have hlocal:=ordinary_induced_physical_edit_of_global R G J Hs (Q.extendedVertices 0) (Q.extendedIndices 0)
    (Lconf+Lcorr+(ordinaryResourceRows K).card+(ordinaryResourceHubs K).card) hglobal
  have hgraph:rawWheelGraph (P.comap f) raw=R.induce ((Q.extendedVertices 0):Set V):=by
    exact ordinary_raw_pair_graph_eq f g P σ
  have hcomm:∀x,f (ρ x)=π (f x):=(marked_vortex_permutation_compatibility Q π hπ 0).1
  have hspoke:rawWheelSpokes ρ d raw j=fun v u=>J (f v) (g u):=by
    convert ordinary_raw_pair_spokes_eq f g π ρ hcomm d σ j using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  intro w
  have hh:=hlocal w
  rw [hgraph,hspoke]
  calc
    _≤Lconf+Lcorr+(ordinaryResourceRows K).card+(ordinaryResourceHubs K).card:=by
      convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    _≤Ledit:=hbudget
end Oberwolfach
