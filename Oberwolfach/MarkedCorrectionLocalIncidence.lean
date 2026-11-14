module

public import Oberwolfach.MarkedFiniteCorrectionIncidence
public import Oberwolfach.MarkedPhysicalAuxiliaryIncidence

@[expose] public section
/-! Sparse correction bounds control physical and auxiliary incidences. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_correction_local_incidence_bound
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V) (H₀ Hₖ:V→U→Prop)
    (FA:Finset (E⊕K)) (FS:Finset (V×U)) (B:ℝ) (hB:0≤B)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hArc:∀v,((FA.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:ℝ)≤B)
    (hRow:∀v,((FS.filter (fun z=>v=z.1)).card:ℝ)≤B)
    (hCol:∀u,((FS.filter (fun z=>z.2=u)).card:ℝ)≤B):
    ∀ physical z,(((markedIncidentEdges tail head ktail khead π H₀ Hₖ physical z).filter
      (fun a=>markedActivePhysical tail head ktail khead π H₀ Hₖ a∈markedFiniteResources tail head ktail khead π FA FS)).card:ℝ)≤6*B := by
  have hArc':∀v,((FA.filter (fun a=>Sum.elim tail ktail a=v∨Sum.elim head khead a=v)).card:ℝ)≤B:=by
    intro v; simpa only [eq_comm] using hArc v
  have hRow':∀v,((FS.filter (fun z=>z.1=v)).card:ℝ)≤B:=by
    intro v; simpa only [eq_comm] using hRow v
  have hphys:=marked_finite_correction_physical_incidence tail head ktail khead π FA FS B hB hArc' hRow' hCol
  intro physical z
  have h:=marked_incidence_bound_from_physical_resources tail head ktail khead π H₀ Hₖ hp
    (markedFiniteResources tail head ktail khead π FA FS) (3*B) hphys physical z
  linarith
end Oberwolfach
