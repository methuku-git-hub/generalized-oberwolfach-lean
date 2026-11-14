module

public import Oberwolfach.MixedOutcomeOrdinarySpokeExclusion
public import Oberwolfach.RetainedMarkedIntervalGeometry

@[expose] public section
/-! Retained marked root labels are avoided by ordinary spokes and by every
raw approximate interval from the same outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retained_labels_avoid_ordinary_and_raw_intervals
    {V U Γ Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [DecidableEq Γ] [Fintype Color]
    (π:Equiv.Perm V) (d:ℕ) (hd:1≤d)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (g₀ g₁:Γ) (hclasses:g₀≠g₁) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (w:U) (j:Color):
    let A:=retainedMarkedIndex π d σ g₀ t J w
    let B:={a:V // rawIntervalColouredStart π d (fun e=>σ (w,e)) a g₁}
    let Y:=markedIntervalRootSet π (fun _:A=>d) Subtype.val
    Disjoint (rawIntervalOrdinaryOuter π d σ j w) Y ∧
    ∀(a:B) (k:Fin (d+1)),(π^k.val) a.val∉Y:=by
  intro A B Y
  have hy:∀x∈Y,∃a:A,x∈permutationWindow π 0 d a.val:=by
    intro x hx
    obtain ⟨a,_,hx⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨k,_,hk⟩:=Finset.mem_image.mp hx
    refine ⟨a,?_⟩
    unfold permutationWindow
    apply Finset.mem_image.mpr
    refine ⟨⟨k.val,by have hk':=k.isLt;change k.val<d at hk';omega⟩,Finset.mem_univ _,?_⟩
    exact hk
  have hgeom:=retained_and_raw_interval_geometry π d hd hnoshort σ g₀ g₁ hclasses t J w
  constructor
  · apply Finset.disjoint_left.mpr
    intro x hx hy'
    obtain ⟨a,ha⟩:=hy x hy'
    have hh:=retained_and_raw_intervals_avoid_ordinary_spokes π d σ g₀ g₁ t J w j (Sum.inl a)
    exact Finset.disjoint_left.mp hh ha hx
  · intro a k hy'
    obtain ⟨b,hb⟩:=hy _ hy'
    have ha:(π^k.val) a.val∈permutationWindow π 0 d a.val:=by
      unfold permutationWindow
      exact Finset.mem_image.mpr ⟨⟨k.val,by have hk:=k.isLt;omega⟩,Finset.mem_univ _,rfl⟩
    have hne:(Sum.inl b:retainedAndRawIntervalIndex π d σ g₀ g₁ t J w)≠Sum.inr a:=by intro h;cases h
    have hh:=hgeom.2 (Sum.inl b) (Sum.inr a) hne
    exact Finset.disjoint_left.mp hh hb ha
end Oberwolfach
