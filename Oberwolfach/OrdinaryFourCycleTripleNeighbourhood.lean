module

public import Oberwolfach.OrdinaryDenseThreeRootTwoHubGeometry

@[expose] public section
/-! Three-neighbourhood input for the four-cycle absorber from the same
bounded-order row event, including repeated vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]
theorem ordinary_four_cycle_triple_neighbourhood
    (P F:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (σ:RawWheelOutcome V U Γ Color)
    (p pmin smin:ℝ) (s:U→Color→ℝ) (j:Color) (α t L β:ℝ) [Nonempty U]
    (hh:3≤h) (hα:0<α) (hL:0≤L)
    (hP:∀ v,(2/3+α)*Fintype.card V≤(P.degree v:ℝ)) (hF:∀ v,(F.degree v:ℝ)≤L)
    (hpmin:0<pmin) (hp:pmin≤p) (hp1:p≤1)
    (hsmin:0<smin) (hsmin1:smin≤1) (hs:∀ u,smin≤s u j)
    (hrows:RawOrdinaryRows P π d h Finset.univ p s j t σ)
    (hmargin:β*Fintype.card V≤(pmin^3*smin^3)*(3*(min α (1/3)))*Fintype.card V-t-3*L):
    ∀ x y z,β*Fintype.card V≤(((rawWheelGraph P σ\F).neighborFinset x∩
      (rawWheelGraph P σ\F).neighborFinset y∩(rawWheelGraph P σ\F).neighborFinset z).card:ℝ) := by
  have hrows3:RawOrdinaryRows P π d 3 Finset.univ p s j t σ:=by
    intro S J hS hJ
    exact hrows S J (by omega) (by omega)
  let u:U:=Classical.choice inferInstance
  have hgeo:=ordinary_dense_three_root_two_hub_geometry P F π d σ p pmin smin s j α t L
    hα hL hP hF hpmin hp hp1 hsmin hsmin1 hs hrows3
  intro x y z
  apply le_trans hmargin
  apply le_trans (hgeo u u x y z)
  have hsub:Finset.univ.filter (fun a=>rawWheelSpokes π d σ j a u∧rawWheelSpokes π d σ j a u∧
      (rawWheelGraph P σ\F).Adj x a∧(rawWheelGraph P σ\F).Adj y a∧(rawWheelGraph P σ\F).Adj z a) ⊆
      ((rawWheelGraph P σ\F).neighborFinset x∩(rawWheelGraph P σ\F).neighborFinset y∩(rawWheelGraph P σ\F).neighborFinset z) := by
    intro a ha
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at ha
    simp only [Finset.mem_inter,SimpleGraph.mem_neighborFinset]
    exact ⟨⟨ha.2.2.1,ha.2.2.2.1⟩,ha.2.2.2.2⟩
  exact_mod_cast Finset.card_le_card hsub
end Oberwolfach
