module

public import Oberwolfach.OrdinaryDeletedEdgesInOldDomain

@[expose] public section

/-! With no retained first-family paths, every vertex on a matched rim
already lies in the package's physical old image. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_package_old_rim_occupancy
    {X V A B J W:Type} [Fintype X] [DecidableEq X] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype J] [DecidableEq J]
    [IsEmpty A]
    {G:SimpleGraph X} (m d:ℕ) (π:Equiv.Perm V) (targetRoot:A⊕B→V)
    (Arc:V→V→Prop) (Avail Reserve:Finset V)
    (Good:W→Prop) (Pack:W→Finset (Finset V)) (Pos:W→B→Finset ℕ) (len:J→ℕ)
    (pk:OrdinaryMatchedResidualHubPackage G m d π targetRoot Arc Avail Reserve Good Pack Pos len):
    ∀edge∈Pack pk.marker,∀v∈edge,
      v∈(pk.data.oldDomain\bufferedPathStrictInterior (fun _:A=>(m+1)*d) pk.inner).image pk.ψ :=by
  have hs₁:pk.data.s₁=∅:=by
    rw [pk.hs₁]
    ext x
    simp only [Finset.notMem_empty,iff_false]
    intro hx
    simp only [firstSumIndices,Finset.mem_image,Finset.mem_univ,true_and] at hx
    obtain ⟨a,_⟩:=hx
    exact isEmptyElim a
  have hstrict:bufferedPathStrictInterior (fun _:A=>(m+1)*d) pk.inner=∅:=by
    ext x
    simp only [Finset.notMem_empty,iff_false]
    intro hx
    obtain ⟨a,_,_⟩:=Finset.mem_biUnion.mp hx
    exact isEmptyElim a
  have hcycles:pk.data.t.biUnion (fun j=>(pk.data.C j).support.toFinset)⊆pk.data.Cembed:=by
    rw [pk.hEmbed]
  intro edge hedge v hv
  obtain ⟨mapped,hmapped,heq⟩:=pk.hAllRims edge hedge
  obtain ⟨e,he,rfl⟩:=Finset.mem_image.mp hmapped
  have hvmap:v∈Sym2.map pk.ψ e:=by
    have hh:v∈(Sym2.map pk.ψ e).toFinset:=by rw [heq];exact hv
    simpa using hh
  obtain ⟨x,hxe,hxv⟩:=Sym2.mem_map.mp hvmap
  have hxold:=ordinary_deleted_edges_endpoints_in_old_domain pk.data hs₁ hcycles e he x hxe
  apply Finset.mem_image.mpr
  refine ⟨x,?_,hxv⟩
  simpa [hstrict] using hxold
end Oberwolfach
