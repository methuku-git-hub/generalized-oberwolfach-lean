module

public import Oberwolfach.RawIntervalHubStartsExpectation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem hub_start_singleton_pattern (π:Equiv.Perm V) (d:ℕ) (g:Γ)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (u:U):
    rawIntervalHubStartCount π d g σ u =
      supportedPatternSum (fun v:V=>{(v,u)}) (fun _=>1)
        (fun _ _=>true) (rawIntervalFamilyStartState π d g) σ := by
  unfold rawIntervalHubStartCount supportedPatternSum
  simp_rw [patternValue_indicator,one_mul]
  apply Finset.sum_congr rfl
  intro v _
  simp

theorem hub_start_singleton_square_sum (u:U) :
    (∑ a:V×U,(∑ v:V,if a∈({(v,u)}:Finset (V×U)) then (1:ℝ) else 0)^2)≤Fintype.card V:=by
  have h (a:V×U):(∑ v:V,if a∈({(v,u)}:Finset (V×U)) then (1:ℝ) else 0)=if a.2=u then 1 else 0:=by
    rcases a with ⟨x,y⟩
    by_cases hy:y=u
    · subst y
      simp [Finset.mem_singleton,Prod.mk.injEq,eq_comm]
    · simp [Finset.mem_singleton,Prod.mk.injEq,hy,Ne.symm hy]
  simp_rw [h]
  rw [Fintype.sum_prod_type]
  simp

variable (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
local notation "μfamily" => rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS

theorem rawIntervalHubStartCount_tail_singleton
    (hn:0<Fintype.card V) (g:Γ) (u:U) (t:ℝ) (ht:0<t):
    (FiniteLaw.pi μfamily).probability (fun σ=>t≤
      |rawIntervalHubStartCount π d g σ u-
        (FiniteLaw.pi μfamily).expectation (fun τ=>rawIntervalHubStartCount π d g τ u)|)≤
      2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(Fintype.card V:ℝ))) := by
  have hn0:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hh:=supportedPatternSum_tail (A:=V×U) (I:=V) (E:=U×RawIntervalCoordinate V) (State:=fun _=>Bool) μfamily (fun v:V=>{(v,u)}) (fun _=>1)
    (by intro v;norm_num) (fun _ _=>true)
    (rawIntervalFamilyCoordinates π d) (rawIntervalFamilyStartState π d g)
    (fun a σ τ ha=>rawIntervalFamilyStartState_supported π d g σ τ a ha)
    (4*(d:ℝ)+3) (Fintype.card V:ℝ) (by positivity) hn0
    (by intro a;exact_mod_cast rawIntervalFamilyCoordinates_card π d a)
    (by intro e;exact_mod_cast rawIntervalFamilyCoordinates_reverse_card π d e)
    (hub_start_singleton_square_sum u) t ht
  have heq:(supportedPatternSum (fun v:V=>{(v,u)}) (fun _=>1)
      (fun _ _=>true) (rawIntervalFamilyStartState (Color:=Color) π d g))=
      (fun σ:RawIntervalFamilyOutcome V U Γ Color=>rawIntervalHubStartCount π d g σ u):=by
    funext σ
    exact (hub_start_singleton_pattern π d g σ u).symm
  rw [heq] at hh
  exact hh
end Oberwolfach
