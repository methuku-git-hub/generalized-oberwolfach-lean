module

public import Oberwolfach.OrdinaryManyRootTwoHubGeometry
public import Oberwolfach.OrdinaryRootDensity
public import Oberwolfach.DenseFourRootNeighbourhood

@[expose] public section
/-! Four-root two-hub geometry for the triangular profile caller. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]
theorem ordinary_dense_four_root_two_hub_geometry
    (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawWheelOutcome V U Γ Color)
    (p pmin smin:ℝ) (s:U→Color→ℝ) (j:Color) (α t L:ℝ)
    (hα:0<α) (hL:0≤L)
    (hP:∀ v,(3/4+α)*Fintype.card V≤(P.degree v:ℝ)) (hF:∀ v,(F.degree v:ℝ)≤L)
    (hpmin:0<pmin) (hp:pmin≤p) (hp1:p≤1)
    (hsmin:0<smin) (hsmin1:smin≤1) (hs:∀ u,smin≤s u j)
    (hrows:RawOrdinaryRows P π d 4 Finset.univ p s j t σ):
    ∀ u u' v₁ v₂ v₃ v₄,
      (pmin^4*smin^4)*(4*(min α (1/4)))*Fintype.card V-t-4*L≤
        ((Finset.univ.filter (fun z=>rawWheelSpokes π d σ j z u ∧ rawWheelSpokes π d σ j z u' ∧
          (rawWheelGraph P σ\F).Adj v₁ z ∧ (rawWheelGraph P σ\F).Adj v₂ z ∧
          (rawWheelGraph P σ\F).Adj v₃ z ∧ (rawWheelGraph P σ\F).Adj v₄ z)).card:ℝ) := by
  intro u u' v₁ v₂ v₃ v₄
  let S:Finset V:={v₁,v₂,v₃,v₄}
  let T:=Finset.univ.filter (fun z=>rawWheelSpokes π d σ j z u ∧ rawWheelSpokes π d σ j z u')
  have hS:S.card≤4:=by
    dsimp [S]
    have h1:=Finset.card_insert_le v₁ ({v₂,v₃,v₄}:Finset V)
    have h2:=Finset.card_insert_le v₂ ({v₃,v₄}:Finset V)
    have h3:=Finset.card_insert_le v₃ ({v₄}:Finset V)
    simp only [Finset.card_singleton] at h3
    omega
  have hx:0<min α (1/4:ℝ):=lt_min hα (by norm_num)
  have hh:=ordinary_many_root_two_hub_geometry P F π d 4 (by norm_num) σ p s j
    (4*(min α (1/4))) (pmin^4*smin^4) t L (by positivity) (by positivity) hL hF
    (dense_four_root_neighbourhood P α hα hP)
    (ordinary_root_density 4 p pmin smin s j hpmin hp hp1 hsmin hsmin1 hs) hrows u u' S hS
  have hset:common T S (fun x=>(rawWheelGraph P σ\F).neighborFinset x)=
      Finset.univ.filter (fun z=>rawWheelSpokes π d σ j z u ∧ rawWheelSpokes π d σ j z u' ∧
        (rawWheelGraph P σ\F).Adj v₁ z ∧ (rawWheelGraph P σ\F).Adj v₂ z ∧
        (rawWheelGraph P σ\F).Adj v₃ z ∧ (rawWheelGraph P σ\F).Adj v₄ z) := by
    ext z
    simp only [mem_common_iff,Finset.mem_filter,Finset.mem_univ,true_and,SimpleGraph.mem_neighborFinset]
    simp [S,T] <;> tauto
  rw [hset] at hh
  exact hh
end Oberwolfach
