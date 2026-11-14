module

public import Oberwolfach.RetainedIntervalIdentities
public import Oberwolfach.MarkedIntervalRootCardinality

@[expose] public section
/-! The marked root sets of the actual trimmed sample have exactly the
uniform load required by the residual degree calculation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

abbrev retainedMarkedIndex (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g:Γ) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g) t) (w:U):Type :=
  {a:V // retainedRawStart π d σ g t J w a g}

theorem retained_marked_root_membership
    (π:Equiv.Perm V) (d:ℕ) (hd:1≤d) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g:Γ) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g) t) (w:U) (v:V):
    v∈markedIntervalRootSet π (fun _ : retainedMarkedIndex π d σ g t J w=>d) Subtype.val ↔
      retainedRawFamilyState π d σ g t J (v,w)=some (Sum.inl g):=by
  classical
  rw [retainedRawFamilyState,retainedIntervalState_interval_iff π d (fun e=>σ (w,e))
    (retainedRawStart π d σ g t J w) (fun _ _ h=>h.1)]
  change v∈markedIntervalRootSet π (fun _ : retainedMarkedIndex π d σ g t J w=>d) Subtype.val ↔
    ∃a,retainedRawStart π d σ g t J w a g ∧ v∈permutationWindow π 0 (d-1) a
  unfold markedIntervalRootSet
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_image]
  constructor
  · rintro ⟨a,i,rfl⟩
    refine ⟨a.val,a.property,?_⟩
    unfold permutationWindow
    apply Finset.mem_image.mpr
    refine ⟨⟨i.val,by have hi:=i.isLt;omega⟩,Finset.mem_univ _,?_⟩
    simp
    rfl
  · rintro ⟨a,ha,hv⟩
    unfold permutationWindow at hv
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hv
    refine ⟨⟨a,ha⟩,⟨i.val,by have hi':i.val<0+(d-1)+1:=i.isLt;omega⟩,?_⟩
    change (π^i.val) a=v at hi
    exact hi

theorem retained_marked_roots_uniform
    (π:Equiv.Perm V) (d:ℕ) (hd:1≤d)
    (hnoshort:∀x l,0<l→l<d→(π^l) x≠x)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (g:Γ) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ g) t):
    ∀v,(Finset.univ.filter (fun w=>v∈markedIntervalRootSet π
      (fun _ : retainedMarkedIndex π d σ g t J w=>d) Subtype.val)).card=d*t:=by
  intro v
  have heq:(Finset.univ.filter (fun w=>v∈markedIntervalRootSet π
      (fun _ : retainedMarkedIndex π d σ g t J w=>d) Subtype.val))=
      Finset.univ.filter (fun w=>retainedRawFamilyState π d σ g t J (v,w)=some (Sum.inl g)):=by
    ext w
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact retained_marked_root_membership π d hd σ g t J w v
  rw [heq]
  exact retainedRawFamily_covered_card π d hd hnoshort σ g t J v
end Oberwolfach
