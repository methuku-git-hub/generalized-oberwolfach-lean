module

public import Oberwolfach.RawIntervalUnassignedHubRestricted

@[expose] public section
/-! Unassigned-spoke concentration at the tested vertex set's size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

theorem hub_start_singleton_weighted_square_sum_local (u:U) (A:Finset V):
    (∑ a:V×U,(∑ v:V,if a∈({(v,u)}:Finset (V×U)) then (if v∈A then (1:ℝ) else 0) else 0)^2)≤A.card:=by
  have h (a:V×U):(∑ v:V,if a∈({(v,u)}:Finset (V×U)) then (if v∈A then (1:ℝ) else 0) else 0)=
      if a.2=u ∧ a.1∈A then 1 else 0:=by
    rcases a with ⟨x,y⟩
    by_cases hy:y=u
    · subst y
      simp [Finset.mem_singleton,Prod.mk.injEq,eq_comm]
    · simp [Finset.mem_singleton,Prod.mk.injEq,hy,Ne.symm hy]
  simp_rw [h]
  rw [Fintype.sum_prod_type]
  have hx (x:V):(∑y:U,(if y=u ∧ x∈A then (1:ℝ) else 0)^2) = if x∈A then 1 else 0 := by
    by_cases hx:x∈A <;> simp [hx]
  simp_rw [hx]
  simp

variable (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
  (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
  (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
local notation "μfamily" => rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS

theorem rawIntervalUnassignedHubCountOn_local_tail
    (u:U) (A:Finset V) (hA:0<A.card) (t:ℝ) (ht:0<t):
    (FiniteLaw.pi μfamily).probability (fun σ=>t≤
      |rawIntervalUnassignedHubCountOn π d σ u A-
        (FiniteLaw.pi μfamily).expectation (fun τ=>rawIntervalUnassignedHubCountOn π d τ u A)|)≤
      2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(A.card:ℝ))) := by
  have hn0:(0:ℝ)<A.card:=by exact_mod_cast hA
  have hh:=supportedPatternSum_tail (A:=V×U) (I:=V) μfamily (fun v=>{(v,u)}) (fun v=>if v∈A then 1 else 0)
    (by intro v;split_ifs <;> norm_num) (fun _ _=>none)
    (rawIntervalFamilyCoordinates π d) (rawIntervalFamilyState π d)
    (fun a σ τ ha=>rawIntervalFamilyState_supported π d σ τ a ha)
    (4*(d:ℝ)+3) (A.card:ℝ) (by positivity) hn0
    (by intro a;exact_mod_cast rawIntervalFamilyCoordinates_card π d a)
    (by intro e;exact_mod_cast rawIntervalFamilyCoordinates_reverse_card π d e)
    (hub_start_singleton_weighted_square_sum_local u A) t ht
  have heq:(supportedPatternSum (fun v:V=>{(v,u)}) (fun v=>if v∈A then 1 else 0)
      (fun _ _=>none) (rawIntervalFamilyState (Γ:=Γ) (Color:=Color) π d))=
      (fun σ:RawIntervalFamilyOutcome V U Γ Color=>rawIntervalUnassignedHubCountOn π d σ u A):=by
    funext σ
    exact (rawIntervalUnassignedHubCountOn_pattern π d σ u A).symm
  rw [heq] at hh
  exact hh
end Oberwolfach
