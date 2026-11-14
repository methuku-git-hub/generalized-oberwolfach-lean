module

public import Oberwolfach.OrdinaryPhysicalSpokeChanges

@[expose] public section
/-! The two directions of a physical spoke edit have bounded degree whenever
the original rows and relevant hub columns have bounded symmetric change. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_restricted_spoke_edit_degree_bounds (H J:V→U→Prop) (B:Finset U) (L:ℝ) (hL:0≤L)
    (hrow:∀v,((changed (B.filter (H v)) (B.filter (J v))).card:ℝ)≤L)
    (hcol:∀u∈B,((changed (Finset.univ.filter (fun v=>H v u))
      (Finset.univ.filter (fun v=>J v u))).card:ℝ)≤L):
    let H₀:=fun v u=>u∈B∧H v u
    let J₀:=fun v u=>u∈B∧J v u;
    (∀z,((ordinaryPhysicalSpokeGraph H₀\ordinaryPhysicalSpokeGraph J₀).degree z:ℝ)≤L) ∧
    (∀z,((ordinaryPhysicalSpokeGraph J₀\ordinaryPhysicalSpokeGraph H₀).degree z:ℝ)≤L):=by
  intro H₀ J₀
  have hr:∀v,((changed (Finset.univ.filter (H₀ v)) (Finset.univ.filter (J₀ v))).card:ℝ)≤L:=by
    intro v
    have heH:Finset.univ.filter (H₀ v)=B.filter (H v):=by ext u;simp [H₀]
    have heJ:Finset.univ.filter (J₀ v)=B.filter (J v):=by ext u;simp [J₀]
    rw [heH,heJ]
    exact hrow v
  have hc:∀u,((changed (Finset.univ.filter (fun v=>H₀ v u))
      (Finset.univ.filter (fun v=>J₀ v u))).card:ℝ)≤L:=by
    intro u
    by_cases hu:u∈B
    · simpa [H₀,J₀,hu] using hcol u hu
    · simpa [H₀,J₀,hu,changed] using hL
  have hr':∀v,((changed (Finset.univ.filter (J₀ v)) (Finset.univ.filter (H₀ v))).card:ℝ)≤L:=by
    intro v
    have hh:=hr v
    simpa only [changed,Finset.union_comm] using hh
  have hc':∀u,((changed (Finset.univ.filter (fun v=>J₀ v u))
      (Finset.univ.filter (fun v=>H₀ v u))).card:ℝ)≤L:=by
    intro u
    have hh:=hc u
    simpa only [changed,Finset.union_comm] using hh
  have h1:=ordinary_physical_spoke_difference_bound H₀ J₀ L
    (by intro v;convert hr v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro u;convert hc u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  have h2:=ordinary_physical_spoke_difference_bound J₀ H₀ L
    (by intro v;convert hr' v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro u;convert hc' u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  constructor
  · intro z;convert h1 z using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro z;convert h2 z using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
