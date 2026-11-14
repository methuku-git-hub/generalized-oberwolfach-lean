module

public import Oberwolfach.RawUnassignedPhysicalNeighbourTests
public import Oberwolfach.RawProtectedExtendingList

@[expose] public section
/-! The physical-neighbourhood concentration event gives a concrete protected
extending list whenever the displayed density and endpoint-loss bounds hold. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def RawNeighbourTestValid {V:Type} (i:RawNeighbourTestIndex V):Prop:=
  match i with
  | some (.inr (.inr (x,y)))=>x≠y
  | _=>True

theorem raw_neighbour_test_concentration_extending_list
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [DecidableEq Γ] [Fintype Color]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (ω:Sym2 V→Fin 6×Bool)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (w:U) (q:U→Γ→ℝ) (s:U→Color→ℝ)
    (α η β t:ℝ) (hα:0≤α) (hη:0≤η) (hβ:0≤β)
    (hprob:η≤1-(∑g,q w g)-(∑j,s w j))
    (hdensity:∀i,RawNeighbourTestValid i→α*Fintype.card V≤(rawApproxNeighbourTestSet P π d ω i).card)
    (hmargin:β*Fintype.card V+t≤α*Fintype.card V*η)
    (hcount:∀i,|rawIntervalUnassignedHubCountOn π d σ w (rawApproxNeighbourTestSet P π d ω i)-
      (rawApproxNeighbourTestSet P π d ω i).card*(1-(∑g,q w g)-(∑j,s w j))|<t):
    IsExtendingList (rawApproxPhysicalRelation P π d ω)
      (Finset.univ.filter (fun x=>rawIntervalFamilyState π d σ (x,w)=none)) β:=by
  have hcountLower:∀i,RawNeighbourTestValid i→β*Fintype.card V≤
      rawIntervalUnassignedHubCountOn π d σ w (rawApproxNeighbourTestSet P π d ω i):=by
    intro i hi
    have hs:=hdensity i hi
    have hc:=abs_lt.mp (hcount i)
    have hn:(0:ℝ)≤Fintype.card V:=by positivity
    have hcard:(0:ℝ)≤(rawApproxNeighbourTestSet P π d ω i).card:=by positivity
    have hp:0≤1-(∑g,q w g)-(∑j,s w j):=le_trans hη hprob
    have hmul:α*Fintype.card V*η≤(rawApproxNeighbourTestSet P π d ω i).card*(1-(∑g,q w g)-(∑j,s w j)):=
      (mul_le_mul_of_nonneg_right hs hη).trans (mul_le_mul_of_nonneg_left hprob hcard)
    linarith
  apply raw_unassigned_list_extending_from_counts π d σ w (rawApproxPhysicalRelation P π d ω) β hβ
  · simpa [rawApproxNeighbourTestSet,RawNeighbourTestValid] using hcountLower none trivial
  · intro x
    simpa [rawApproxNeighbourTestSet,RawNeighbourTestValid] using hcountLower (some (.inl x)) trivial
  · intro y
    simpa [rawApproxNeighbourTestSet,RawNeighbourTestValid] using hcountLower (some (.inr (.inl y))) trivial
  · intro x y hxy
    simpa [rawApproxNeighbourTestSet,RawNeighbourTestValid] using hcountLower (some (.inr (.inr (x,y)))) hxy

theorem raw_neighbour_test_concentration_protected_list
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [DecidableEq Γ] [Fintype Color]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (ω:Sym2 V→Fin 6×Bool)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (g₀ g₁:Γ) (r:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) r) (w:U) (q:U→Γ→ℝ) (s:U→Color→ℝ)
    (α η β lam t:ℝ) (hα:0≤α) (hη:0≤η) (hβ:0≤β) (hlam:0≤lam)
    (hprob:η≤1-(∑g,q w g)-(∑j,s w j))
    (hdensity:∀i,RawNeighbourTestValid i→α*Fintype.card V≤(rawApproxNeighbourTestSet P π d ω i).card)
    (hmargin:β*Fintype.card V+t≤α*Fintype.card V*η)
    (hcount:∀i,|rawIntervalUnassignedHubCountOn π d σ w (rawApproxNeighbourTestSet P π d ω i)-
      (rawApproxNeighbourTestSet P π d ω i).card*(1-(∑g,q w g)-(∑j,s w j))|<t)
    (hbudget:lam*Fintype.card V+(Fintype.card (retainedAndRawIntervalIndex π d σ g₀ g₁ r J w):ℝ)≤β*Fintype.card V):
    IsExtendingList (rawApproxPhysicalRelation P π d ω)
      (rawIntervalProtectedUnassignedList π d σ g₀ g₁ r J w) lam:=by
  exact raw_protected_unassigned_list_extends π d σ g₀ g₁ r J w _ β lam hlam hbudget
    (raw_neighbour_test_concentration_extending_list P π d ω σ w q s α η β t hα hη hβ hprob hdensity hmargin hcount)
end Oberwolfach
