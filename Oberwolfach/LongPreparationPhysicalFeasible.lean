module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic

@[expose] public section
/-! The five physical states use the manuscript's prescribed probabilities;
their total equals the original density parameter. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_preparation_physical_feasible {U:Type} [Fintype U]
    (D ρ s t:ℝ) (hD:0<D) (hρ:0≤ρ) (hρ1:ρ≤1) (hs:0≤s) (ht:0≤t)
    (a b:U→ℝ) (ha:∀ u,0≤a u) (hb:∀ u,0≤b u)
    (hrest:∀ u,0≤1-s-t-a u-b u) (hsize:ρ*D=2*Fintype.card U):
    let p:=ρ*s/2
    let k:=ρ*t/2
    let p₂:=(∑ u,b u)/D
    let k₂:=(∑ u,a u)/D
    let u:=2*(∑ v,(1-s-t-a v-b v))/D;
    0≤p ∧ 0≤k ∧ 0≤p₂ ∧ 0≤k₂ ∧ 0≤u ∧
      2*p+2*k+2*p₂+2*k₂+u=ρ ∧ 2*p+2*k+2*p₂+2*k₂+u≤1:=by
  intro p k p₂ k₂ u
  have haSum:0≤∑ v,a v:=Finset.sum_nonneg (fun v _=>ha v)
  have hbSum:0≤∑ v,b v:=Finset.sum_nonneg (fun v _=>hb v)
  have huSum:0≤∑ v,(1-s-t-a v-b v):=Finset.sum_nonneg (fun v _=>hrest v)
  have hsum:(∑ v,(1-s-t-a v-b v))=(Fintype.card U:ℝ)*(1-s-t)-(∑ v,a v)-(∑ v,b v):=by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    ring
  have heq:2*p+2*k+2*p₂+2*k₂+u=ρ:=by
    dsimp [p,k,p₂,k₂,u]
    rw [hsum]
    field_simp
    nlinarith [hsize]
  refine ⟨?_,?_,?_,?_,?_,heq,?_⟩
  · dsimp [p];positivity
  · dsimp [k];positivity
  · dsimp [p₂];exact div_nonneg hbSum hD.le
  · dsimp [k₂];exact div_nonneg haSum hD.le
  · dsimp [u];positivity
  · rw [heq];exact hρ1
end Oberwolfach
