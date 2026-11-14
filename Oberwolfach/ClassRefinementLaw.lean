module

public import Oberwolfach.FiniteLawSigmaProjection
public import Oberwolfach.FiniteLawMap

@[expose] public section
/-! A single categorical class choice, refined conditionally, has exactly the
original categorical projection. Distinct class views remain coupled. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

namespace FiniteLaw

def optional {A:Type} [Fintype A] (p:ℝ) (hp:0≤p) (hp1:p≤1) (μ:FiniteLaw A):FiniteLaw (Option A) where
  mass x:=match x with | none=>1-p | some a=>p*μ.mass a
  nonneg x:=by
    cases x with
    | none => exact sub_nonneg.mpr hp1
    | some a => exact mul_nonneg hp (μ.nonneg a)
  total:=by
    rw [Fintype.sum_option]
    simp only [←Finset.mul_sum,μ.total,mul_one]
    ring
end FiniteLaw

def classRefinedView {C A:Type} [DecidableEq C] (a:C) (z:Σ _:C,A):Option A:=
  if z.1=a then some z.2 else none

theorem categorical_refinement_class_marginal {k:ℕ} {A:Type} [Fintype A]
    (ρ:Fin k→ℝ) (hρ:∀ a,0≤ρ a) (htotal:∑ a,ρ a=1)
    (ν:Fin k→FiniteLaw A) (a:Fin k):
    let μ:=(FiniteLaw.categorical ρ hρ htotal).sigma ν;
    μ.map (classRefinedView (A:=A) a)=FiniteLaw.optional (ρ a) (hρ a)
      (by have h:=Finset.single_le_sum (fun b _=>hρ b) (Finset.mem_univ a);linarith) (ν a):=by
  intro μ
  apply finiteLaw_ext
  intro x
  cases x with
  | none =>
    simp only [FiniteLaw.map,FiniteLaw.optional]
    rw [Fintype.sum_sigma]
    have hsum:(∑ c:Fin k,((if c=a then ρ c else 0)+(if c=a then 0 else ρ c)))=1:=by
      calc
        _ = ∑ c:Fin k,ρ c:=by
          apply Finset.sum_congr rfl
          intro c _
          by_cases h:c=a <;> simp [h]
        _ = 1:=htotal
    have hs0:(∑ c:Fin k,if c=a then ρ c else 0)=ρ a:=by simp
    have hs:(∑ c:Fin k,if c=a then 0 else ρ c)=1-ρ a:=by
      rw [Finset.sum_add_distrib,hs0] at hsum
      linarith
    calc
      _ = ∑ c:Fin k,if c=a then 0 else ρ c:=by
        apply Finset.sum_congr rfl
        intro c _
        by_cases hc:c=a
        · simp [classRefinedView,hc]
        · simp [classRefinedView,hc,μ,FiniteLaw.sigma,FiniteLaw.categorical,←Finset.mul_sum,(ν c).total]
      _ = _:=hs
  | some x =>
    simp only [FiniteLaw.map,FiniteLaw.optional]
    rw [Fintype.sum_sigma]
    have heach (c:Fin k):
        (∑ z:A,if classRefinedView a ⟨c,z⟩=some x then μ.mass ⟨c,z⟩ else 0)=
          if c=a then ρ a*(ν a).mass x else 0:=by
      by_cases hc:c=a
      · subst c
        simp [classRefinedView,μ,FiniteLaw.sigma,FiniteLaw.categorical]
      · simp [classRefinedView,hc]
    calc
      _ = ∑ c:Fin k,if c=a then ρ a*(ν a).mass x else 0:=by
        apply Finset.sum_congr rfl
        intro c _
        convert heach c using 1
        apply Finset.sum_congr rfl
        intro y _
        by_cases h:classRefinedView a ⟨c,y⟩=some x <;> simp [h]
      _ = _:=by simp
end Oberwolfach

