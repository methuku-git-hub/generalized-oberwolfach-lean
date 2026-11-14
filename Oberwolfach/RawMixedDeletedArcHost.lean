module

public import Oberwolfach.RawMixedPhysicalArcHost
public import Oberwolfach.RawMarkedRimDeletion

@[expose] public section
/-! A sampled physical arc surviving a rim deletion lies in the host and
avoids every deleted edge, including shifted rim coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_mixed_deleted_arc_host
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (P Del:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (raw:RawMarkedOutcome V U Γ Color)
    (x y:V) (h:rawMixedPhysicalArc P π d (rawMarkedDeleteRims raw Del.edgeFinset) x y):
    P.Adj x y ∧ ¬Del.Adj x y:=by
  have hh:P.Adj x y ∧ (∃mark,rawMarkedDeleteRims raw Del.edgeFinset (Sum.inl s(x,y))=
      some (mark,orientationBit x y)):=by
    rcases h with h|h
    · have hh:=(markedPhysicalRim_eq_one_iff P π (3*d) (fun e=>rawMarkedDeleteRims raw Del.edgeFinset (Sum.inl e)) false x y).mp h
      exact ⟨by simpa using hh.2.1, false, by simpa using hh.2.2⟩
    · have hh:=(markedPhysicalRim_eq_one_iff P π (3*d) (fun e=>rawMarkedDeleteRims raw Del.edgeFinset (Sum.inl e)) true x (π.symm y)).mp h
      refine ⟨by simpa using hh.2.1, true, ?_⟩
      convert hh.2.2 using 1 <;> congr! 8 <;> simp
  refine ⟨hh.1,?_⟩
  intro hDel
  obtain ⟨mark,hmark⟩:=hh.2
  have he:s(x,y)∈Del.edgeFinset:=SimpleGraph.mem_edgeFinset.mpr hDel
  simp [rawMarkedDeleteRims,he] at hmark
end Oberwolfach
