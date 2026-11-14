module

public import Oberwolfach.VortexSizeBounds
public import Oberwolfach.MarkedExpandedDegreeEvent
public import Oberwolfach.UniformStartRetentionMinimum
public import Oberwolfach.RawStartCounts

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_selected_marked_indegree_retained_start_balance
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U]
    (P:SimpleGraph V) (D d m:ℕ) (hD:0<D) (hd:0<d) (hm:0<m)
    (π:Equiv.Perm V) (σ:RawIntervalFamilyOutcome V U Γ Color) (g:Γ)
    (ω:Sym2 V→Fin 6×Bool) (s err:ℝ) (herr:0≤err)
    (hstart:∀v,|((rawStartHubSet π d σ g v).card:ℝ)-
      (∑_w:U,(s/(m:ℝ))/(d:ℝ))|≤err)
    (hhead:∀v,|((∑x,sampledColourOrientation P ω 1 x v:ℕ):ℝ)-
      (initialIndexDensity U D*(s/(m:ℝ))/2)*(D:ℝ)|≤err):
    ∀v,|((∑x,sampledColourOrientation P ω 1 x v:ℕ):ℝ)-
      (d:ℝ)*(startRetentionMinimum (rawStartHubSet π d σ g):ℝ)|≤err+(d:ℝ)*err :=by
  have hdR:0<(d:ℝ):=by exact_mod_cast hd
  have hDR:(D:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt hD)
  have hmean:(∑_w:U,(s/(m:ℝ))/(d:ℝ))=(Fintype.card U:ℝ)*(s/(m:ℝ))/(d:ℝ):=by simp;ring
  have hcenter:initialIndexDensity U D*(s/(m:ℝ))/2*(D:ℝ)=
      (d:ℝ)*((Fintype.card U:ℝ)*(s/(m:ℝ))/(d:ℝ)):=by
    dsimp [initialIndexDensity]
    field_simp
  have hmin:=startRetentionMinimum_close (rawStartHubSet π d σ g)
    ((Fintype.card U:ℝ)*(s/(m:ℝ))/(d:ℝ)) err (by intro v;simpa only [hmean] using hstart v)
  have hl:=mul_le_mul_of_nonneg_left (abs_le.mp hmin).1 hdR.le
  have hu:=mul_le_mul_of_nonneg_left (abs_le.mp hmin).2 hdR.le
  intro v
  have hv:=hhead v
  rw [hcenter] at hv
  apply abs_le.mpr
  constructor <;> linarith [abs_le.mp hv]
end Oberwolfach
