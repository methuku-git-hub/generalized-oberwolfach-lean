module

public import Oberwolfach.RawIntervalUnassignedGeometry
public import Oberwolfach.MixedOutcomeOrdinarySpokeExclusion

@[expose] public section
/-! The unassigned raw list, with the extended interval endpoints removed,
avoids all ordinary-spoke labels and all extended retained/raw intervals. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def rawIntervalProtectedUnassignedList
    {V U Γ Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [DecidableEq Γ] [Fintype Color]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g₀ g₁:Γ) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (w:U):Finset V:=
  (Finset.univ.filter (fun x=>rawIntervalFamilyState π d σ (x,w)=none))\
    Finset.univ.image (fun i:retainedAndRawIntervalIndex π d σ g₀ g₁ t J w=>
      (π^d) (retainedAndRawIntervalRoot π d σ g₀ g₁ t J w i))

theorem raw_interval_protected_unassigned_avoids_labels
    {V U Γ Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [DecidableEq Γ] [Fintype Color]
    (π:Equiv.Perm V) (d:ℕ) (hd:1≤d) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g₀ g₁:Γ) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (w:U) (color:Color):
    let L:=rawIntervalProtectedUnassignedList π d σ g₀ g₁ t J w
    let root:=retainedAndRawIntervalRoot π d σ g₀ g₁ t J w
    Disjoint L (rawIntervalOrdinaryOuter π d σ color w) ∧
    ∀i (j:Fin (d+1)),(π^j.val) (root i)∉L:=by
  intro L root
  constructor
  · apply Finset.disjoint_left.mpr
    intro x hx ho
    have hn:rawIntervalFamilyState π d σ (x,w)=none:=(Finset.mem_filter.mp (Finset.mem_sdiff.mp hx).1).2
    have hs:rawIntervalFamilyState π d σ (x,w)=some (Sum.inr color):=by
      simpa only [rawIntervalOrdinaryOuter,Finset.mem_filter,Finset.mem_univ,true_and] using ho
    rw [hn] at hs
    cases hs
  · intro i j hx
    have hn:rawIntervalState π d (fun e=>σ (w,e)) ((π^j.val) (root i))=none:=
      (Finset.mem_filter.mp (Finset.mem_sdiff.mp hx).1).2
    have hnot:∀g,¬rawIntervalCovered π d (fun e=>σ (w,e)) ((π^j.val) (root i)) g:=
      (rawIntervalState_none_iff π d _ _).mp hn |>.1
    have hstart:∃g,rawIntervalColouredStart π d (fun e=>σ (w,e)) (root i) g:=by
      cases i with
      | inl a=>exact ⟨g₀,a.property.1⟩
      | inr a=>exact ⟨g₁,a.property⟩
    obtain ⟨g,hg⟩:=hstart
    by_cases hj:j.val=d
    · have hend:(π^j.val) (root i)∈Finset.univ.image (fun i:retainedAndRawIntervalIndex π d σ g₀ g₁ t J w=>(π^d) (root i)):=by
        apply Finset.mem_image.mpr
        refine ⟨i,Finset.mem_univ _,?_⟩
        simpa [hj]
      exact (Finset.mem_sdiff.mp hx).2 hend
    · have hlt:j.val<d:=by have hh:=j.isLt;omega
      have hw:(π^j.val) (root i)∈permutationWindow π 0 (d-1) (root i):=by
        unfold permutationWindow
        exact Finset.mem_image.mpr ⟨⟨j.val,by omega⟩,Finset.mem_univ _,rfl⟩
      exact hnot g ⟨root i,hg,hw⟩

theorem raw_interval_protected_unassigned_loss
    {V U Γ Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [DecidableEq Γ] [Fintype Color]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g₀ g₁:Γ) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (w:U):
    ((Finset.univ.filter (fun x=>rawIntervalFamilyState π d σ (x,w)=none))\
      rawIntervalProtectedUnassignedList π d σ g₀ g₁ t J w).card≤
        Fintype.card (retainedAndRawIntervalIndex π d σ g₀ g₁ t J w):=by
  let E:=Finset.univ.image (fun i:retainedAndRawIntervalIndex π d σ g₀ g₁ t J w=>
    (π^d) (retainedAndRawIntervalRoot π d σ g₀ g₁ t J w i))
  have hsub:((Finset.univ.filter (fun x=>rawIntervalFamilyState π d σ (x,w)=none))\
      rawIntervalProtectedUnassignedList π d σ g₀ g₁ t J w)⊆E:=by
    intro x hx
    simp only [rawIntervalProtectedUnassignedList,Finset.mem_sdiff,not_and,not_not] at hx
    exact hx.2 hx.1
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
end Oberwolfach
