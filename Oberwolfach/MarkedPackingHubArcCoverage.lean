module

public import Oberwolfach.MarkedPackingHubRimPartition
public import Oberwolfach.MarkedWheelWalkPhysicalArcSet

@[expose] public section
/-! Hub factors whose wheels are exactly the packing's hub fibres cover
exactly the packing's ordered physical rim arcs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_packing_hub_arc_coverage
    {V U E K:Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ Hₖ:V→U→Prop}
    (P:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ))
    (M:∀u:U,Finset (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u))
    (himage:∀u,(M u).image (hubCycleWheel u)=P.filter (fun W=>W.2.val=u)):
    Finset.univ.biUnion (fun u=>(M u).biUnion (fun C=>
      markedCyclePhysicalArcs tail head ktail khead m π b (hubCycleAsMarked u C)))=
    P.biUnion (fun W=>markedCyclePhysicalArcs tail head ktail khead m π b W.1) := by
  ext e
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨u,C,hC,he⟩
    have hW:hubCycleWheel u C∈P:=by
      have hh:hubCycleWheel u C∈(M u).image (hubCycleWheel u):=Finset.mem_image.mpr ⟨C,hC,rfl⟩
      rw [himage u] at hh
      exact (Finset.mem_filter.mp hh).1
    exact ⟨hubCycleWheel u C,hW,he⟩
  · rintro ⟨W,hW,he⟩
    let u:=W.2.val
    have hf:W∈P.filter (fun Z=>Z.2.val=u):=Finset.mem_filter.mpr ⟨hW,rfl⟩
    rw [←himage u] at hf
    obtain ⟨C,hC,hCW⟩:=Finset.mem_image.mp hf
    refine ⟨u,C,hC,?_⟩
    change e∈markedCyclePhysicalArcs tail head ktail khead m π b (hubCycleWheel u C).1
    rw [hCW]
    exact he
end Oberwolfach
