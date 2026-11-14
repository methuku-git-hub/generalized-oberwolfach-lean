module

public import Oberwolfach.ExpandedClassOrientationDegrees
public import Oberwolfach.SampledOrientationDegreeStability
public import Oberwolfach.SampledClassDegreeSum

@[expose] public section
/-! The five state-degree estimates and bounded graph edits give the initial
outdegree error for routing on the regularised class graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem expanded_class_initial_outdegree_error
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (P S:SimpleGraph V) (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (mass:Fin 6→ℝ) (ρ D t b ε:ℝ) (m:ℕ) (hρ:0≤ρ)
    (hmass:(∑a∈({0,1,2,3,4}:Finset (Fin 6)),mass a)=ρ)
    (hsize:ρ*D=2*m)
    (hdegree:∀v,|(P.degree v:ℝ)-D|≤ε)
    (hcol:∀a v,|((∑w,sampledColourOrientation P (fun e=>σ (Sum.inl e)) a v w:ℕ):ℝ)-
      mass a/2*P.degree v|≤t)
    (hedit:∀v,((changed ((longPhysicalStateGraph P σ {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤b):
    ∀v,|((∑w,sampledOrientation S (fun e=>(σ (Sum.inl e)).2) v w:ℕ):ℝ)-m|≤5*t+ρ/2*ε+b:=by
  intro v
  let T:Finset (Fin 6):={0,1,2,3,4}
  let f:=fun a:Fin 6=>((∑w,sampledColourOrientation P (fun e=>σ (Sum.inl e)) a v w:ℕ):ℝ)
  let g:=fun a:Fin 6=>mass a/2*P.degree v
  have hs:=sampled_class_degree_sum_bound T f g t (fun a _=>hcol a v)
  have htc:(T.card:ℝ)=5:=by norm_num [T]
  rw [htc] at hs
  have hf:((∑w,sampledOrientation (longPhysicalStateGraph P σ {0,1,2,3,4})
      (fun e=>(σ (Sum.inl e)).2) v w:ℕ):ℝ)=∑a∈T,f a:=by
    rw [expanded_class_orientation_degrees]
    push_cast
    dsimp only [T,f]
    apply Finset.sum_congr rfl
    intro a _
    simp only [Nat.cast_sum]
  have hg:(∑a∈T,g a)=ρ/2*P.degree v:=by
    dsimp only [g]
    rw [←Finset.sum_mul]
    have hm:(∑a∈T,mass a/2)=ρ/2:=by
      rw [←Finset.sum_div]
      exact congrArg (fun x:ℝ=>x/2) hmass
    rw [hm]
  rw [←hf,hg] at hs
  have he:=sampled_orientation_degree_stability S (longPhysicalStateGraph P σ {0,1,2,3,4}) (fun e=>(σ (Sum.inl e)).2) v
  have hc:((changed (S.neighborFinset v) ((longPhysicalStateGraph P σ {0,1,2,3,4}).neighborFinset v)).card:ℝ)≤b:=by
    have hh:=hedit v
    simpa [changed,Finset.union_comm] using hh
  have hsE:=he.trans hc
  have hcentre:|ρ/2*(P.degree v:ℝ)-m|≤ρ/2*ε:=by
    have hmul:=mul_le_mul_of_nonneg_left (hdegree v) (show 0≤ρ/2 by positivity)
    have heq:ρ/2*(P.degree v:ℝ)-m=(ρ/2)*((P.degree v:ℝ)-D):=by nlinarith [hsize]
    rw [heq,abs_mul,abs_of_nonneg (show 0≤ρ/2 by positivity)]
    exact hmul
  have ht1:=abs_sub_le ((∑w,sampledOrientation S (fun e=>(σ (Sum.inl e)).2) v w:ℕ):ℝ)
    ((∑w,sampledOrientation (longPhysicalStateGraph P σ {0,1,2,3,4}) (fun e=>(σ (Sum.inl e)).2) v w:ℕ):ℝ) (ρ/2*P.degree v)
  have ht2:=abs_sub_le ((∑w,sampledOrientation S (fun e=>(σ (Sum.inl e)).2) v w:ℕ):ℝ) (ρ/2*P.degree v) m
  linarith
end Oberwolfach
