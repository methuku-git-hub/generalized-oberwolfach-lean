module

public import Mathlib.Tactic

@[expose] public section
/-! An explicit local balance and boundary allowance, to make quantitative
comparisons with the earlier correction scale reviewable. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def markedExplicitJointLocalCap (m h:ℕ) (etaBal x:ℝ):ℝ:=
  min (x/(16*((h:ℝ)+1)))
    (min (x/(16*((m+4:ℕ):ℝ))) (etaBal/(16*((m+4:ℕ):ℝ))))

theorem marked_explicit_joint_balance_boundary_budget
    (m h:ℕ) (etaBal x:ℝ) (hη:0<etaBal) (hx:0<x):
    let c:=markedExplicitJointLocalCap m h etaBal x;
    0<c ∧ 2*(h:ℝ)*c≤x/4 ∧
      ∀(V:Type) [Fintype V] [DecidableEq V] (A:Finset V),
      2*(c*A.card)+((m+2:ℕ):ℝ)*(c*A.card)≤
        min ((x/4)*Fintype.card V) ((etaBal/2)*A.card) :=by
  intro c
  let M:ℝ:=(m+4:ℕ)
  have hM:0<M:=by dsimp [M];positivity
  have hc:0<c:=by dsimp [c,markedExplicitJointLocalCap];positivity
  have hhBound:c≤x/(16*((h:ℝ)+1)):=by dsimp [c,markedExplicitJointLocalCap];exact min_le_left _ _
  have hxBound:c≤x/(16*M):=by dsimp [c,markedExplicitJointLocalCap,M];exact (min_le_right _ _).trans (min_le_left _ _)
  have hηBound:c≤etaBal/(16*M):=by dsimp [c,markedExplicitJointLocalCap,M];exact (min_le_right _ _).trans (min_le_right _ _)
  have hcost:2*(h:ℝ)*c≤x/4:=by
    have hh:=mul_le_mul_of_nonneg_left hhBound (show 0≤2*(h:ℝ) by positivity)
    have hd:0<16*((h:ℝ)+1):=by positivity
    have hmul:16*((h:ℝ)+1)*c≤x:=by simpa only [mul_comm] using (le_div_iff₀ hd).mp hhBound
    have hn:(0:ℝ)≤h:=Nat.cast_nonneg _
    nlinarith [mul_nonneg hn hc.le]
  have hxcap:M*c≤x/16:=by
    have hh:=(le_div_iff₀ (show 0<16*M by positivity)).mp hxBound
    nlinarith
  have hηcap:M*c≤etaBal/16:=by
    have hh:=(le_div_iff₀ (show 0<16*M by positivity)).mp hηBound
    nlinarith
  refine ⟨hc,hcost,?_⟩
  intro V _ _ A
  have hA:(0:ℝ)≤A.card:=Nat.cast_nonneg _
  have hcard:(A.card:ℝ)≤Fintype.card V:=by exact_mod_cast Finset.card_le_univ A
  have h1:=mul_le_mul_of_nonneg_right hxcap hA
  have h2:=mul_le_mul_of_nonneg_right hηcap hA
  have h3:=mul_le_mul_of_nonneg_left hcard (show 0≤x/16 by positivity)
  have heq:2*(c*A.card)+((m+2:ℕ):ℝ)*(c*A.card)=M*c*A.card:=by dsimp [M];push_cast;ring
  rw [heq]
  apply le_min <;> nlinarith [mul_nonneg hx.le hA,mul_nonneg hη.le hA]
end Oberwolfach
