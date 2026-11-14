module

public import Oberwolfach.LongDualResidualEligibility
public import Oberwolfach.LongPreparationPhysicalContainment
public import Oberwolfach.MarkedExpandedPhysicalLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V]
local instance dualCoverageDecEq : DecidableEq V := Classical.decEq V

theorem long_dual_residual_eligibility_from_required_coverage
    (G S Small Used:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:Sym2 V→Fin 6×Bool) (Mhost:V→V→ℕ)
    (hphysical:∀x y,Mhost x y+Mhost y x=if S.Adj x y then 1 else 0)
    (hUsed:Used≤Small):
    let D:=fun x y=>Mhost x y=1 ∧
      markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω e)) true x (π.symm y)≠1
    (longCloseRequiredGraph S π d D (fun x y=>Used.Adj x y))≤Small→
    ∀x y,Mhost x y=1→¬Small.Adj x y→
      longOrdinaryArcEligible π d (x,y) ∨ longMarkedArcEligible π d (x,y):=by
  intro D hRequired x y hM hSmall
  by_cases hOrd:longOrdinaryArcEligible π d (x,y)
  · exact Or.inl hOrd
  · right
    by_contra hMark
    have hClose:PermutationClose π (3*d) x y:=Classical.not_not.mp hOrd
    have hMarkClose:PermutationClose π (3*d) x (π.symm y):=Classical.not_not.mp hMark
    have hS:S.Adj x y:=by
      by_contra hn
      have hh:=hphysical x y
      rw [if_neg hn,hM] at hh
      omega
    have hNotRaw:markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω e)) true x (π.symm y)≠1:=by
      intro h
      exact ((markedPhysicalRim_eq_one_iff G π (3*d) _ true x (π.symm y)).mp h).1 hMarkClose
    have hNotUsed:¬Used.Adj x y:=fun h=>hSmall (hUsed h)
    apply hSmall
    apply hRequired
    exact ⟨hS,hClose,Or.inl ⟨⟨hM,hNotRaw⟩,hNotUsed⟩⟩

/-- A used edge need not be embedded: it is enough that its fixed direction
already admits one of the two types. -/
theorem long_dual_residual_eligibility_from_used_or_required
    (G S Small Used:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:Sym2 V→Fin 6×Bool) (Mhost:V→V→ℕ)
    (hphysical:∀x y,Mhost x y+Mhost y x=if S.Adj x y then 1 else 0)
    (hUsed:∀x y,Mhost x y=1→Used.Adj x y→
      longOrdinaryArcEligible π d (x,y) ∨ longMarkedArcEligible π d (x,y)):
    let D:=fun x y=>Mhost x y=1 ∧
      markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω e)) true x (π.symm y)≠1
    (longCloseRequiredGraph S π d D (fun x y=>Used.Adj x y))≤Small→
    ∀x y,Mhost x y=1→¬Small.Adj x y→
      longOrdinaryArcEligible π d (x,y) ∨ longMarkedArcEligible π d (x,y):=by
  intro D hRequired x y hM hSmall
  by_cases hOrd:longOrdinaryArcEligible π d (x,y)
  · exact Or.inl hOrd
  · right
    by_contra hMark
    have hClose:PermutationClose π (3*d) x y:=Classical.not_not.mp hOrd
    have hMarkClose:PermutationClose π (3*d) x (π.symm y):=Classical.not_not.mp hMark
    have hS:S.Adj x y:=by
      by_contra hn
      have hh:=hphysical x y
      rw [if_neg hn,hM] at hh
      omega
    have hNotRaw:markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω e)) true x (π.symm y)≠1:=by
      intro h
      exact ((markedPhysicalRim_eq_one_iff G π (3*d) _ true x (π.symm y)).mp h).1 hMarkClose
    have hNotUsed:¬Used.Adj x y:=by
      intro h
      rcases hUsed x y hM h with ho|hm
      · exact hOrd ho
      · exact hMark hm
    apply hSmall
    apply hRequired
    exact ⟨hS,hClose,Or.inl ⟨⟨hM,hNotRaw⟩,hNotUsed⟩⟩

end Oberwolfach
