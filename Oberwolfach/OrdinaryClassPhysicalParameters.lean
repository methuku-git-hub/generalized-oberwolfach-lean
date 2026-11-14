module

public import Oberwolfach.FiniteHighEventsCommon

@[expose] public section
/-! Numerical physical probabilities for an ordinary class, using the
actual fixed index marginals and the class density. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
open scoped BigOperators

theorem ordinary_class_physical_parameters {U:Type} [Fintype U]
    (ρ D s b₀:ℝ) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D) (hs:0≤s) (hb₀:0≤b₀)
    (a b u:U→ℝ) (ha:∀ w,0≤a w) (hb:∀ w,b₀≤b w) (hu:∀ w,0≤u w)
    (hrow:∀ w,s+a w+b w+u w=1) (hsize:ρ*D=2*(Fintype.card U:ℝ)):
    let p:=ρ*s/2
    let p₂:=(∑ w,(a w+b w))/D
    let unassigned:=2*(∑ w,u w)/D;
    0≤p ∧ 0≤p₂ ∧ 0≤unassigned ∧
    2*p+2*p₂+unassigned=ρ ∧ 2*p+2*p₂+unassigned≤1 ∧
    (2*p)*D=2*(Fintype.card U:ℝ)*s ∧
    ρ*b₀/2≤p₂ ∧
    unassigned=ρ*((∑ w,u w)/(Fintype.card U:ℝ)) := by
  intro p p₂ unassigned
  have hU:(0:ℝ)<Fintype.card U:=by nlinarith
  have hsum:(Fintype.card U:ℝ)*s+(∑ w,a w)+(∑ w,b w)+(∑ w,u w)=Fintype.card U:=by
    have hh:(∑ w:U,(s+a w+b w+u w))=∑ _w:U,(1:ℝ):=by
      apply Finset.sum_congr rfl
      intro w _
      exact hrow w
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using hh
  have hasum:0≤∑ w,a w:=Finset.sum_nonneg (fun w _=>ha w)
  have hbsum:(Fintype.card U:ℝ)*b₀≤∑ w,b w:=by
    have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun w _=>hb w)
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using hh
  have husum:0≤∑ w,u w:=Finset.sum_nonneg (fun w _=>hu w)
  have hp:0≤p:=by dsimp [p];positivity
  have hbnonneg:0≤∑ w,b w:=by
    have hh:(0:ℝ)≤(Fintype.card U:ℝ)*b₀:=mul_nonneg hU.le hb₀
    exact hh.trans hbsum
  have hp₂:0≤p₂:=by
    dsimp [p₂];rw [Finset.sum_add_distrib]
    exact div_nonneg (add_nonneg hasum hbnonneg) hD.le
  have hu':0≤unassigned:=by dsimp [unassigned];positivity
  have hbal:2*p+2*p₂+unassigned=ρ:=by
    dsimp [p,p₂,unassigned]
    rw [Finset.sum_add_distrib]
    field_simp
    have hh:=congrArg (fun x:ℝ=>x*s) hsize
    nlinarith
  refine ⟨hp,hp₂,hu',hbal,hbal.le.trans hρ1,?_,?_,?_⟩
  · dsimp [p]
    have hh:=congrArg (fun x:ℝ=>x*s) hsize
    nlinarith
  · dsimp [p₂]
    rw [Finset.sum_add_distrib]
    apply (le_div_iff₀ hD).2
    have hh:=congrArg (fun x:ℝ=>x*b₀) hsize
    nlinarith
  · dsimp [unassigned]
    field_simp
    have hh:=congrArg (fun x:ℝ=>x*(∑ w,u w)) hsize
    nlinarith
end Oberwolfach
