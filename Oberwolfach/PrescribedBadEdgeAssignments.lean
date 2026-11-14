module

public import Oberwolfach.PrescribedAssignedMatchingDisjoint

@[expose] public section
/-! The oriented edges of a physical graph, partitioned by an index
assignment, retain every physical edge exactly in its assigned factor. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]

def prescribedAssignedArcs (K:SimpleGraph V) (assign:Sym2 V→I) (orient:Sym2 V→V×V) (i:I):Finset (V×V):=
  (K.edgeFinset.filter (fun e=>assign e=i)).image orient

theorem prescribed_assigned_arcs_physical (K:SimpleGraph V) (assign:Sym2 V→I) (orient:Sym2 V→V×V)
    (horient:∀e∈K.edgeFinset,prescribedArcPhysical (orient e)=e):
    (∀ i e,e∈(prescribedAssignedArcs K assign orient i).image prescribedArcPhysical→
      e∈K.edgeFinset ∧ assign e=i) ∧
    (∀ e∈K.edgeFinset,e∈(prescribedAssignedArcs K assign orient (assign e)).image prescribedArcPhysical) ∧
    PairwisePhysicalDisjoint (fun i=>(prescribedAssignedArcs K assign orient i).image prescribedArcPhysical) := by
  have hassign:∀ i e,e∈(prescribedAssignedArcs K assign orient i).image prescribedArcPhysical→
      e∈K.edgeFinset ∧ assign e=i:=by
    intro i e he
    obtain ⟨a,ha,hae⟩:=Finset.mem_image.mp he
    obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp ha
    have hb':b∈K.edgeFinset ∧ assign b=i:=Finset.mem_filter.mp hb
    have heq:e=b:=hae.symm.trans (horient b hb'.1)
    simpa [heq] using hb'
  refine ⟨hassign,?_,(prescribed_assigned_matchings_disjoint _ K assign hassign).2⟩
  intro e he
  apply Finset.mem_image.mpr
  refine ⟨orient e,?_,horient e he⟩
  apply Finset.mem_image.mpr
  refine ⟨e,Finset.mem_filter.mpr ⟨he,rfl⟩,rfl⟩
end Oberwolfach
