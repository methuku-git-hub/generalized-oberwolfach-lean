module

public import Oberwolfach.RawIntervalUnassignedHubRestricted
public import Oberwolfach.RawIntervalUnassignedProbability
public import Oberwolfach.RawIntervalHubStartsSingleton

@[expose] public section
/-! Counts on a fixed vertex set in one hub column. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def rawIntervalReservedLabelHubCountOn (π:Equiv.Perm V) (d:ℕ)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (u:U) (j:Color) (A:Finset V):ℝ:=
  ∑ v∈A,if rawIntervalFamilyState π d σ (v,u)=some (Sum.inr j) then 1 else 0

theorem rawIntervalReservedLabelHubCountOn_pattern (π:Equiv.Perm V) (d:ℕ)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (u:U) (j:Color) (A:Finset V):
    rawIntervalReservedLabelHubCountOn π d σ u j A=
      supportedPatternSum (fun v:V=>{(v,u)}) (fun v=>if v∈A then 1 else 0)
        (fun _ _=>some (Sum.inr j)) (rawIntervalFamilyState π d) σ:=by
  unfold rawIntervalReservedLabelHubCountOn supportedPatternSum
  simp_rw [patternValue_indicator]
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_mem,Finset.univ_inter]
  apply Finset.sum_congr rfl
  intro v _
  simp

variable (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
local notation "μfamily" => rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS

theorem rawIntervalReservedLabelHubCountOn_expectation
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x) (u:U) (j:Color) (A:Finset V):
    (FiniteLaw.pi μfamily).expectation (fun σ=>rawIntervalReservedLabelHubCountOn π d σ u j A)=
      (A.card:ℝ)*s u j:=by
  unfold FiniteLaw.expectation rawIntervalReservedLabelHubCountOn
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h (v:V):
      (∑ σ,(FiniteLaw.pi μfamily).mass σ * (if rawIntervalFamilyState π d σ (v,u)=some (Sum.inr j) then (1:ℝ) else 0))=
        s u j:=by
    have hh:=rawIntervalFamily_label_probability π d hd q hq hQ s hs hS hnoshort (v,u) j
    unfold FiniteLaw.probability at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro σ _
    split_ifs <;> simp_all
  simp_rw [h]
  simp [Finset.sum_const,nsmul_eq_mul]

theorem rawIntervalReservedLabelHubCountOn_tail
    (hn:0<Fintype.card V) (u:U) (j:Color) (A:Finset V) (t:ℝ) (ht:0<t):
    (FiniteLaw.pi μfamily).probability (fun σ=>t≤
      |rawIntervalReservedLabelHubCountOn π d σ u j A-
        (FiniteLaw.pi μfamily).expectation (fun τ=>rawIntervalReservedLabelHubCountOn π d τ u j A)|)≤
      2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(Fintype.card V:ℝ))) := by
  have hn0:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hh:=supportedPatternSum_tail (A:=V×U) (I:=V) (E:=U×RawIntervalCoordinate V) (State:=fun _=>Option (Γ⊕Color)) μfamily (fun v:V=>{(v,u)}) (fun v=>if v∈A then 1 else 0)
    (by intro v;split_ifs <;> norm_num) (fun _ _=>some (Sum.inr j))
    (rawIntervalFamilyCoordinates π d) (rawIntervalFamilyState π d)
    (fun a σ τ ha=>rawIntervalFamilyState_supported π d σ τ a ha)
    (4*(d:ℝ)+3) (Fintype.card V:ℝ) (by positivity) hn0
    (by intro a;exact_mod_cast rawIntervalFamilyCoordinates_card π d a)
    (by intro e;exact_mod_cast rawIntervalFamilyCoordinates_reverse_card π d e)
    (hub_start_singleton_weighted_square_sum u A) t ht
  have heq:(supportedPatternSum (fun v:V=>{(v,u)}) (fun v=>if v∈A then 1 else 0)
      (fun _ _=>some (Sum.inr j)) (rawIntervalFamilyState (Γ:=Γ) (Color:=Color) π d))=
      (fun σ:RawIntervalFamilyOutcome V U Γ Color=>rawIntervalReservedLabelHubCountOn π d σ u j A):=by
    funext σ
    exact (rawIntervalReservedLabelHubCountOn_pattern π d σ u j A).symm
  rw [heq] at hh
  exact hh
end Oberwolfach
