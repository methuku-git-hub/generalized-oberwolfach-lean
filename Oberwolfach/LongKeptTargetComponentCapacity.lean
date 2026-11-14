module

public import Oberwolfach.CycleComponentFrequency
public import Oberwolfach.ApproximateSelectedCapacity
public import Oberwolfach.LongAssignedSeedTargets

@[expose] public section
/-! The retained vertex fraction never asks for more cycles than the
prescribed factor actually contains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_kept_target_le_component_count (hn:0<n)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (θ:ℝ) (i:Fin K) (u:U):
    let T:=Finset.univ.filter (fun C:(F u).ConnectedComponent=>Fintype.card C=i.val+1)
    0≤longAssignedKeptFraction F hF K θ i u*(n:ℝ)/((i.val+1:ℕ):ℝ) ∧
      longAssignedKeptFraction F hF K θ i u*(n:ℝ)/((i.val+1:ℕ):ℝ)≤T.card :=by
  intro T
  let f:=ordinaryAssignedFraction F hF K u (some i)
  have hf:0≤f:=by dsimp [f,ordinaryAssignedFraction];positivity
  have hkept:0≤longAssignedKeptFraction F hF K θ i u ∧
      longAssignedKeptFraction F hF K θ i u≤f:=by
    dsimp [longAssignedKeptFraction]
    split_ifs <;> constructor <;> simp_all only [f,le_refl]
  have hr:0<((i.val+1:ℕ):ℝ):=by positivity
  constructor
  · exact div_nonneg (mul_nonneg hkept.1 (by positivity)) hr.le
  · have h:=mul_le_mul_of_nonneg_right hkept.2 (show (0:ℝ)≤n by positivity)
    have hd:=div_le_div_of_nonneg_right h hr.le
    have heq:f*(n:ℝ)/((i.val+1:ℕ):ℝ)=(T.card:ℝ):=by
      simpa only [f,ordinaryAssignedFraction,T] using long_preparation_fraction_component_count hn (F u) (hF u) i
    exact hd.trans_eq heq
end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_selected_ordinary_count_le_components (hn:0<n)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (θ lam:ℝ) (hlamθ:lam≤θ) (i:Fin K) (u:U) (a:ℕ):
    let T:=Finset.univ.filter (fun C:(F u).ConnectedComponent=>Fintype.card C=i.val+1)
    let t:=longAssignedKeptFraction F hF K θ i u*(n:ℝ)/((i.val+1:ℕ):ℝ)
    |((a:ℝ)-(1-θ)*t)|≤lam*t → a≤T.card :=by
  intro T t herr
  have hcap:=long_kept_target_le_component_count hn F hF θ i u
  exact approximate_selected_real_target_le_capacity a T.card t θ lam hcap.1 hcap.2 hlamθ herr
end Oberwolfach
