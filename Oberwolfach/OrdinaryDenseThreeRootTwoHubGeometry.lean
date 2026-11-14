module

public import Oberwolfach.OrdinaryManyRootTwoHubGeometry
public import Oberwolfach.OrdinaryRootDensity
public import Oberwolfach.DenseThreeRootNeighbourhood

@[expose] public section
/-! Three-root two-hub geometry for the four-cycle profile caller. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]
theorem ordinary_dense_three_root_two_hub_geometry
    (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawWheelOutcome V U Γ Color)
    (p pmin smin:ℝ) (s:U→Color→ℝ) (j:Color) (α t L:ℝ)
    (hα:0<α) (hL:0≤L)
    (hP:∀ v,(2/3+α)*Fintype.card V≤(P.degree v:ℝ)) (hF:∀ v,(F.degree v:ℝ)≤L)
    (hpmin:0<pmin) (hp:pmin≤p) (hp1:p≤1)
    (hsmin:0<smin) (hsmin1:smin≤1) (hs:∀ u,smin≤s u j)
    (hrows:RawOrdinaryRows P π d 3 Finset.univ p s j t σ):
    ∀ u u' v₁ v₂ v₃,
      (pmin^3*smin^3)*(3*(min α (1/3)))*Fintype.card V-t-3*L≤
        ((Finset.univ.filter (fun z=>rawWheelSpokes π d σ j z u ∧ rawWheelSpokes π d σ j z u' ∧
          (rawWheelGraph P σ\F).Adj v₁ z ∧ (rawWheelGraph P σ\F).Adj v₂ z ∧
          (rawWheelGraph P σ\F).Adj v₃ z)).card:ℝ) := by
  intro u u' v₁ v₂ v₃
  let S:Finset V:={v₁,v₂,v₃}
  let T:=Finset.univ.filter (fun z=>rawWheelSpokes π d σ j z u ∧ rawWheelSpokes π d σ j z u')
  have hS:S.card≤3:=by
    dsimp [S]
    have h1:=Finset.card_insert_le v₁ ({v₂,v₃}:Finset V)
    have h2:=Finset.card_insert_le v₂ ({v₃}:Finset V)
    simp only [Finset.card_singleton] at h2
    omega
  have hx:0<min α (1/3:ℝ):=lt_min hα (by norm_num)
  have hh:=ordinary_many_root_two_hub_geometry P F π d 3 (by norm_num) σ p s j
    (3*(min α (1/3))) (pmin^3*smin^3) t L (by positivity) (by positivity) hL hF
    (dense_three_root_neighbourhood P α hα hP)
    (ordinary_root_density 3 p pmin smin s j hpmin hp hp1 hsmin hsmin1 hs) hrows u u' S hS
  have hset:common T S (fun x=>(rawWheelGraph P σ\F).neighborFinset x)=
      Finset.univ.filter (fun z=>rawWheelSpokes π d σ j z u ∧ rawWheelSpokes π d σ j z u' ∧
        (rawWheelGraph P σ\F).Adj v₁ z ∧ (rawWheelGraph P σ\F).Adj v₂ z ∧
        (rawWheelGraph P σ\F).Adj v₃ z) := by
    ext z
    simp only [mem_common_iff,Finset.mem_filter,Finset.mem_univ,true_and,SimpleGraph.mem_neighborFinset]
    simp [S,T] <;> tauto
  rw [hset] at hh
  exact hh
end Oberwolfach
