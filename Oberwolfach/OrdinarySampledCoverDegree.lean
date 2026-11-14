module

public import Oberwolfach.BoundaryReserveMaximumDegree
public import Oberwolfach.OrdinaryRootCoverData

@[expose] public section
/-! A cover chosen before the fresh coins loses only its retained boundary
edges from the sampled matching classes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def OrdinarySampledCoverDegreeGood (E:SimpleGraph (V⊕U)) (p δ:ℝ) (σ:Sym2 (V⊕U)→Bool):Prop :=
  ∀w,((retainedGraph E σ).degree w:ℝ)≤p*E.degree w+δ*Fintype.card (V⊕U)

theorem ordinary_sampled_cover_degree_high_probability
    (p δ:ℝ) (hp:0≤p) (hp1:p≤1) (hδ:0<δ) (q:ℕ):
    ∃N:ℕ,∀(V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card (V⊕U)→∀E:SimpleGraph (V⊕U),
    1-1/(Fintype.card (V⊕U):ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp hp1)).probability
        (OrdinarySampledCoverDegreeGood E p δ):=by
  obtain ⟨N,hN⟩:=retained_graph_degrees_common_event q δ hδ
  refine ⟨N,?_⟩
  intro V U _ _ _ _ hn E
  apply (hN (V⊕U) hn E p hp hp1).trans
  apply finiteLaw_probability_mono
  intro σ hs w
  have hh:=(abs_lt.mp (hs w)).2
  linarith only [hh]

theorem ordinary_sampled_cover_boundary_degree
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell p δ:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W r η ell) (σ:Sym2 (V⊕U)→Bool)
    (hp:0≤p) (hgood:OrdinarySampledCoverDegreeGood (ordinaryPhysicalGraph D.rim D.spokes) p δ σ):
    ∀w∉ordinaryInnerVertices X Z,
      (((ordinaryPhysicalGraph D.rim D.spokes)⊓retainedGraph (ordinaryBoundaryGraph Q H X Z) σ).degree w:ℝ)≤
        p*ell+δ*Fintype.card (V⊕U):=by
  intro w hw
  let E:=ordinaryPhysicalGraph D.rim D.spokes
  let R:=retainedGraph (ordinaryBoundaryGraph Q H X Z) σ
  have hsub:E⊓R≤retainedGraph E σ:=by
    intro x y hxy
    exact ⟨hxy.1,hxy.2.2⟩
  have hdeg:(((E⊓R).degree w):ℝ)≤((retainedGraph E σ).degree w:ℝ):=by
    exact_mod_cast SimpleGraph.degree_le_of_le hsub (v:=w)
  have hrate:=mul_le_mul_of_nonneg_left (D.outside_degree w hw) hp
  have hrate':p*(E.degree w:ℝ)≤p*ell:=by
    convert hrate using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hh:((retainedGraph E σ).degree w:ℝ)≤p*(E.degree w:ℝ)+δ*Fintype.card (V⊕U):=by
    convert hgood w using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hf:(((E⊓R).degree w):ℝ)≤p*ell+δ*Fintype.card (V⊕U):=by
    linarith only [hdeg,hh,hrate']
  convert hf using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
