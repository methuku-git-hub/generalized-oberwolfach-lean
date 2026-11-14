module

public import Oberwolfach.LongResidualOrientationArcIdentity

@[expose] public section
/-! Exact edge descriptions at each hub identify the physical union of the
canonical arcs with the old and newly embedded edge sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_packed_arc_physical_union
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U]
    (arcs:U→Finset (V×V)) (old new:U→Finset (Sym2 V))
    (h:∀u,(arcs u).image (fun a=>s(a.1,a.2))=old u∪new u):
    (Finset.univ.biUnion arcs).image (fun a=>s(a.1,a.2))=
      (Finset.univ.biUnion old)∪(Finset.univ.biUnion new):=by
  ext e
  simp only [Finset.mem_image,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_union]
  constructor
  · rintro ⟨a,⟨u,ha⟩,rfl⟩
    have hh:s(a.1,a.2)∈old u∪new u:=by
      rw [←h u]
      exact Finset.mem_image.mpr ⟨a,ha,rfl⟩
    rcases Finset.mem_union.mp hh with ho|hn
    · exact Or.inl ⟨u,ho⟩
    · exact Or.inr ⟨u,hn⟩
  · rintro (⟨u,hu⟩|⟨u,hu⟩)
    all_goals
      have hh:e∈(arcs u).image (fun a=>s(a.1,a.2)):=by
        rw [h u]
        simp_all
      obtain ⟨a,ha,he⟩:=Finset.mem_image.mp hh
      exact ⟨a,⟨u,ha⟩,he⟩

end Oberwolfach
