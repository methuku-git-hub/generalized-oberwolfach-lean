module

public import Oberwolfach.RetainedMarkedIntervalGeometry
public import Oberwolfach.MarkedIntervalEndpointSeparation
public import Oberwolfach.MarkedIntervalSuccessorSeparation

@[expose] public section
/-! The matching input identities and geometry on the same retained sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem retained_marked_matching_inputs
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (g:Γ) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ g) t):
    let k:=fun w (_:retainedMarkedIndex π d σ g t J w)=>d
    let a:=fun w (j:retainedMarkedIndex π d σ g t J w)=>j.val
    let Y:=fun w=>markedIntervalRootSet π (k w) (a w)
    let B:=fun w=>Finset.univ.image (fun j=>(π^d) (a w j))
    (∀w j,0<k w j) ∧ (∀w j,k w j≤d) ∧
    (∀w j,Function.Injective (fun i:Fin (k w j+1)=>(π^i.val) (a w j))) ∧
    (∀w j l,j≠l→Disjoint (permutationWindow π 0 (k w j) (a w j))
      (permutationWindow π 0 (k w l) (a w l))) ∧
    (∀v,(Finset.univ.filter (fun w=>v∈Y w)).card=d*t) ∧
    (∀w,Disjoint (Y w) (B w)) ∧ (∀w,(Y w).image π⊆Y w ∪ B w) ∧
    (∀w v,v∈Y w↔retainedRawFamilyState π d σ g t J (v,w)=some (Sum.inl g)):=by
  intro k a Y B
  have hgeom:=retained_marked_interval_geometry π d (by omega) hnoshort σ g t J
  refine ⟨?_,?_,hgeom.1,hgeom.2.1,?_,?_,?_,?_⟩
  · intro w j;exact lt_of_lt_of_le (by decide : 0<2) hd
  · intro w j;exact le_rfl
  · intro v;exact retained_marked_roots_uniform π d (by omega)
      (fun x l hl hld=>hnoshort x l hl (by omega)) σ g t J v
  · intro w;exact marked_interval_roots_disjoint_endpoints π (k w) (a w) (hgeom.1 w) (hgeom.2.1 w)
  · intro w;exact marked_interval_successor_subset π (k w) (a w)
  · intro w v;exact retained_marked_root_membership π d (by omega) σ g t J w v
end Oberwolfach
