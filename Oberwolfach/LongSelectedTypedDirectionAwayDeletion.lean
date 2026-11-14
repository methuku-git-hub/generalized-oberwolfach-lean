module

public import Oberwolfach.LongProtectedSampleArcResidual

@[expose] public section
/-! The protected correction fixes the direction of every selected inner
edge.  The physical edge therefore determines its original typed arc. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance selectedTypedDirectionAwayDecEq : DecidableEq V := Classical.decEq V

theorem long_selected_typed_direction_away_from_deletion
    (G S Del:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (M:V→V→ℕ)
    (hphysical:∀x y,M x y+M y x=if S.Adj x y then 1 else 0)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M≤Del):
    ∀x y,(longSelectedPhysicalGraph G π d ω).Adj x y→¬Del.Adj x y→M x y=1→
      markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) false x y=1 ∨
      markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) true x (π.symm y)=1:=by
  intro x y hSel hNoDel hM
  let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedMarkedCollapse e (ω e)
  change x≠y ∧ ({x,y}:Finset V)∈
    Finset.univ.image (markedPhysicalEdge (fun e:MarkedSampleArc G π (3*d) (fun e=>raw (Sum.inl e)) false=>e.val.1)
      (fun e=>e.val.2) (fun e:MarkedSampleArc G π (3*d) (fun e=>raw (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2) π) at hSel
  obtain ⟨z,_,hz⟩:=Finset.mem_image.mp hSel.2
  have hno:M y x≠1:=by
    intro h
    have hp:=hphysical x y
    split_ifs at hp <;> omega
  cases z with
  | inl z =>
    have hp:({z.val.1,z.val.2}:Finset V)={x,y}:=hz
    have he: (z.val.1=x ∧ z.val.2=y) ∨ (z.val.1=y ∧ z.val.2=x):=by
      apply Set.pair_eq_pair_iff.mp
      simpa only [Finset.coe_pair] using congrArg (fun A:Finset V=>(A:Set V)) hp
    rcases he with ⟨h₁,h₂⟩|⟨h₁,h₂⟩
    · left
      simpa only [h₁,h₂,raw,rawExpandedMarkedCollapse] using z.property
    · have hraw:=long_selected_ordinary_raw_direction G π d (fun e=>ω (Sum.inl e)) z.val.1 z.val.2 z.property
      have hdir:=long_sampled_state_direction_preserved G Del ω M 0 (by decide) hcorrect z.val.1 z.val.2 hraw.1 (by simpa only [h₁,h₂] using (fun h=>hNoDel h.symm))
      exact False.elim (hno (by simpa only [h₁,h₂] using hdir))
  | inr z =>
    have hp:({z.val.1,π z.val.2}:Finset V)={x,y}:=hz
    have he: (z.val.1=x ∧ π z.val.2=y) ∨ (z.val.1=y ∧ π z.val.2=x):=by
      apply Set.pair_eq_pair_iff.mp
      simpa only [Finset.coe_pair] using congrArg (fun A:Finset V=>(A:Set V)) hp
    rcases he with ⟨h₁,h₂⟩|⟨h₁,h₂⟩
    · right
      have hz₂:z.val.2=π.symm y:=by apply π.injective; simpa using h₂
      simpa only [h₁,hz₂,raw,rawExpandedMarkedCollapse] using z.property
    · have hz₂:z.val.2=π.symm x:=by apply π.injective; simpa using h₂
      have hraw:=long_selected_marked_raw_direction G π d (fun e=>ω (Sum.inl e)) z.val.1 (π z.val.2) (by simpa only [Equiv.symm_apply_apply,raw,rawExpandedMarkedCollapse] using z.property)
      have hdir:=long_sampled_state_direction_preserved G Del ω M 1 (by decide) hcorrect z.val.1 (π z.val.2) hraw.1 (by simpa only [h₁,h₂] using (fun h=>hNoDel h.symm))
      exact False.elim (hno (by simpa only [h₁,h₂] using hdir))
end Oberwolfach
