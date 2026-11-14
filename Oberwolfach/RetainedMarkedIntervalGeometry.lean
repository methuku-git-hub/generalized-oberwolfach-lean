module

public import Oberwolfach.RetainedMarkedRootUniformity

@[expose] public section
/-! The retained starts give the disjoint extended intervals and injective
orbits used by the reserved-factor degree and spoke-count lemmas. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem retained_marked_interval_geometry
    (π:Equiv.Perm V) (d:ℕ) (hd:1≤d)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (g:Γ) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ g) t):
    (∀w (j:retainedMarkedIndex π d σ g t J w),
      Function.Injective (fun i:Fin (d+1)=>(π^i.val) j.val)) ∧
    (∀w (j l:retainedMarkedIndex π d σ g t J w),j≠l→
      Disjoint (permutationWindow π 0 d j.val) (permutationWindow π 0 d l.val)) ∧
    (∀v z,(Finset.univ.filter (fun w=>v∈markedIntervalRootSet π
      (fun _ : retainedMarkedIndex π d σ g t J w=>d) Subtype.val)).card=
      (Finset.univ.filter (fun w=>z∈markedIntervalRootSet π
      (fun _ : retainedMarkedIndex π d σ g t J w=>d) Subtype.val)).card):=by
  refine ⟨?_,?_,?_⟩
  · intro w j
    apply permutation_short_interval_injective π (d+1) ?_ j.val
    intro x l hl hld
    exact hnoshort x l hl (by omega)
  · intro w j l hjl
    have hj:=j.property.1.1
    have hl:=l.property.1.1
    exact rawInterval_extended_disjoint π d (fun x=>σ (w,Sum.inl x)) j.val l.val hj hl
      (fun h=>hjl (Subtype.ext h))
  · intro v z
    rw [retained_marked_roots_uniform π d hd (fun x l hl hld=>hnoshort x l hl (by omega)) σ g t J v,
      retained_marked_roots_uniform π d hd (fun x l hl hld=>hnoshort x l hl (by omega)) σ g t J z]
end Oberwolfach
