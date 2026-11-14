module

public import Oberwolfach.FiniteConvexDistance
public import Oberwolfach.ConvexEnergyCoordinateSplit

@[expose] public section

/-! Projection and fibre estimates for the actual disagreement vectors. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I J Ω : Type*} [Fintype I]

def configurationTail (x : Option I → Ω) (i : I) : Ω := x (some i)

def configurationProjection (A : Finset (Option I → Ω)) : Finset (I → Ω) :=
  A.image configurationTail

def configurationFibre (A : Finset (Option I → Ω)) (a : Ω) : Finset (I → Ω) :=
  (A.filter (fun y=>y none=a)).image configurationTail

theorem convexDistanceSq_projection
    (A : Finset (Option I → Ω)) (hA : A.Nonempty) (x : Option I → Ω) :
    convexDistanceSq A x≤
      convexDistanceSq (configurationProjection A) (configurationTail x)+1 := by
  have hh := finiteHullEnergy_coordinate_projection (disagreementVector x) A hA (by
    intro y _
    unfold disagreementVector
    split_ifs <;> norm_num)
  unfold convexDistanceSq configurationProjection
  rw [finiteHullEnergy_image]
  exact hh

theorem convexDistanceSq_fibre_mix
    (A : Finset (Option I → Ω)) (x : Option I → Ω)
    (hF : (configurationFibre A (x none)).Nonempty)
    {θ : ℝ} (hθ0 : 0≤θ) (hθ1 : θ≤1) :
    convexDistanceSq A x≤
      θ*convexDistanceSq (configurationFibre A (x none)) (configurationTail x)+
      (1-θ)*convexDistanceSq (configurationProjection A) (configurationTail x)+(1-θ)^2 := by
  have hB : (A.filter (fun y=>y none=x none)).Nonempty :=
    Finset.image_nonempty.mp hF
  have hA : A.Nonempty := hB.mono (Finset.filter_subset _ _)
  have hh := finiteHullEnergy_coordinate_mix (disagreementVector x) A
    (A.filter (fun y=>y none=x none)) hA (Finset.filter_subset _ _) hB
    (by
      intro y _
      unfold disagreementVector
      split_ifs <;> norm_num)
    (by
      intro y hy
      have hyx := (Finset.mem_filter.mp hy).2
      simp only [disagreementVector,hyx,ite_true])
    hθ0 hθ1
  unfold convexDistanceSq configurationFibre configurationProjection
  rw [finiteHullEnergy_image,finiteHullEnergy_image]
  exact hh

theorem convexDistanceSq_reindex [Fintype J] (e : I ≃ J)
    (A : Finset (J → Ω)) (x : J → Ω) :
    convexDistanceSq (A.image (fun y i=>y (e i))) (fun i=>x (e i))=
      convexDistanceSq A x := by
  unfold convexDistanceSq
  rw [finiteHullEnergy_image]
  exact finiteHullEnergy_reindex e (disagreementVector x) A

end Oberwolfach
