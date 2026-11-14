module

public import Oberwolfach.PrescribedBadEdgeAssignments

@[expose] public section
/-! Orienting a family of pairwise vertex-disjoint physical edges yields an
oriented matching with exactly those physical edges. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]

theorem prescribed_assigned_arcs_are_matchings (K:SimpleGraph V) (assign:Sym2 V→I) (orient:Sym2 V→V×V)
    (horient:∀e∈K.edgeFinset,prescribedArcPhysical (orient e)=e)
    (hmatching:∀i,∀ e∈K.edgeFinset,∀f∈K.edgeFinset,assign e=i→assign f=i→e≠f→Disjoint e.toFinset f.toFinset):
    ∀ i,IsPrescribedOrientedMatching (prescribedAssignedArcs K assign orient i) := by
  intro i
  constructor
  · intro a ha
    obtain ⟨e,he,rfl⟩:=Finset.mem_image.mp ha
    have heK:e∈K.edgeFinset:=(Finset.mem_filter.mp he).1
    intro hloop
    have heq:=horient e heK
    have hdiag:e.IsDiag:=by
      rw [←heq]
      simp [prescribedArcPhysical,hloop]
    exact (K.not_isDiag_of_mem_edgeFinset heK) hdiag
  · intro a ha b hb hab
    obtain ⟨e,he,haeq⟩:=Finset.mem_image.mp ha
    obtain ⟨f,hf,hbeq⟩:=Finset.mem_image.mp hb
    have heK:=Finset.mem_filter.mp he
    have hfK:=Finset.mem_filter.mp hf
    have hef:e≠f:=by
      intro h;subst f
      exact hab (haeq.symm.trans hbeq)
    have hh:=hmatching i e heK.1 f hfK.1 heK.2 hfK.2 hef
    rw [←horient e heK.1,←horient f hfK.1] at hh
    simpa [prescribedArcPhysical,Sym2.toFinset_mk_eq,haeq,hbeq] using hh
end Oberwolfach
