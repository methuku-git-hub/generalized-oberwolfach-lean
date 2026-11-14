module

public import Oberwolfach.RetainedAndRawIntervalGeometry
public import Oberwolfach.RawIntervalActualReservedMatching

@[expose] public section
/-! In the original interval outcome, every ordinary spoke is outside every
extended retained or raw interval of the same hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retained_and_raw_intervals_avoid_ordinary_spokes
    {V U Γ Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] [Fintype Γ] [DecidableEq Γ] [Fintype Color]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g₀ g₁:Γ) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (w:U) (j:Color):
    let root:=retainedAndRawIntervalRoot π d σ g₀ g₁ t J w
    ∀i,Disjoint (permutationWindow π 0 d (root i)) (rawIntervalOrdinaryOuter π d σ j w):=by
  intro root i
  have hcol:∃g,rawIntervalColouredStart π d (fun e=>σ (w,e)) (root i) g:=by
    cases i with
    | inl a=>exact ⟨g₀,a.property.1⟩
    | inr a=>exact ⟨g₁,a.property⟩
  obtain ⟨g,hg⟩:=hcol
  apply Finset.disjoint_left.mpr
  intro x hx ho
  have hstate:rawIntervalState π d (fun e=>σ (w,e)) x=some (Sum.inr j):=by
    simpa only [rawIntervalOrdinaryOuter,Finset.mem_filter,Finset.mem_univ,true_and,rawIntervalFamilyState] using ho
  have hnb:¬rawIntervalBlocked π d (fun e=>σ (w,e)) x:=(rawIntervalState_label_iff π d _ x j).mp hstate |>.1
  exact hnb ⟨g,root i,hg,hx⟩
end Oberwolfach
