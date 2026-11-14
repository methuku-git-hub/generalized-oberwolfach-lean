module

public import Oberwolfach.RawReservedLabelExtendingList
public import Oberwolfach.RawReservedSpokeList
public import Oberwolfach.RawSelectedPhysicalNeighbourTests
public import Oberwolfach.RawNeighbourTestsExtendingList
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

theorem raw_reserved_selected_neighbour_concentration_extending_list
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [DecidableEq Γ] [Fintype Color]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (ω:Sym2 V→Fin 6×Bool)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (w:U) (color:Color) (s:U→Color→ℝ)
    (α η β t:ℝ) (hα:0≤α) (hη:0≤η) (hβ:0≤β)
    (hprob:η≤s w color)
    (hdensity:∀i,RawNeighbourTestValid i→α*Fintype.card V≤(rawSelectedNeighbourTestSet P π d ω i).card)
    (hmargin:β*Fintype.card V+t≤α*Fintype.card V*η)
    (hcount:∀i,|rawIntervalReservedLabelHubCountOn π d σ w color (rawSelectedNeighbourTestSet P π d ω i)-
      (rawSelectedNeighbourTestSet P π d ω i).card*s w color|<t):
    IsExtendingList (rawSelectedPhysicalRelation P π d ω)
      (Finset.univ.filter (fun x=>rawIntervalFamilyState π d σ (x,w)=some (Sum.inr color))) β:=by
  have hcountLower:∀i,RawNeighbourTestValid i→β*Fintype.card V≤
      rawIntervalReservedLabelHubCountOn π d σ w color (rawSelectedNeighbourTestSet P π d ω i):=by
    intro i hi
    have hs:=hdensity i hi
    have hc:=abs_lt.mp (hcount i)
    have hn:(0:ℝ)≤Fintype.card V:=by positivity
    have hcard:(0:ℝ)≤(rawSelectedNeighbourTestSet P π d ω i).card:=by positivity
    have hmul:α*Fintype.card V*η≤(rawSelectedNeighbourTestSet P π d ω i).card*s w color:=
      (mul_le_mul_of_nonneg_right hs hη).trans (mul_le_mul_of_nonneg_left hprob hcard)
    linarith
  have hsize:β*Fintype.card V≤rawIntervalReservedLabelHubCountOn π d σ w color Finset.univ:=by
    simpa [rawSelectedNeighbourTestSet,RawNeighbourTestValid] using hcountLower none trivial
  have hout:∀x,β*Fintype.card V≤rawIntervalReservedLabelHubCountOn π d σ w color
      (directedOutNeighbours (rawSelectedPhysicalRelation P π d ω) x):=by
    intro x; simpa [rawSelectedNeighbourTestSet,RawNeighbourTestValid] using hcountLower (some (.inl x)) trivial
  have hin:∀y,β*Fintype.card V≤rawIntervalReservedLabelHubCountOn π d σ w color
      (directedInNeighbours (rawSelectedPhysicalRelation P π d ω) y):=by
    intro y; simpa [rawSelectedNeighbourTestSet,RawNeighbourTestValid] using hcountLower (some (.inr (.inl y))) trivial
  have hcommon:∀x y,x≠y→β*Fintype.card V≤rawIntervalReservedLabelHubCountOn π d σ w color
      (directedOutNeighbours (rawSelectedPhysicalRelation P π d ω) x∩directedInNeighbours (rawSelectedPhysicalRelation P π d ω) y):=by
    intro x y hxy; simpa [rawSelectedNeighbourTestSet,RawNeighbourTestValid] using hcountLower (some (.inr (.inr (x,y)))) hxy
  have hext:=raw_reserved_label_list_extending_from_counts π d σ w color (rawSelectedPhysicalRelation P π d ω) β hβ hsize hout hin hcommon
  convert hext using 1 <;> congr 1 <;> ext x <;> simp

end Oberwolfach
