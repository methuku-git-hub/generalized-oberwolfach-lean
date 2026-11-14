module

public import Oberwolfach.OrdinaryMatchedResidualHubPackage

@[expose] public section
/-! With no retained marked starts, the package's protected old domain is
the whole old domain and avoids all selected reference-spoke labels. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_matched_package_old_avoids_reserve_when_empty
    {X V A B J W:Type} [Fintype X] [DecidableEq X] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype J] [DecidableEq J]
    (G:SimpleGraph X) (m d:ℕ) (π:Equiv.Perm V) (root:A⊕B→V)
    (Arc:V→V→Prop) (Avail Reserve:Finset V) (Good:W→Prop)
    (Pack:W→Finset (Finset V)) (Pos:W→B→Finset ℕ) (len:J→ℕ)
    (p:OrdinaryMatchedResidualHubPackage G m d π root Arc Avail Reserve Good Pack Pos len)
    (hempty:IsEmpty A):Disjoint (p.data.oldDomain.image p.ψ) Reserve :=by
  have hInt:bufferedPathStrictInterior (fun _:A=>(m+1)*d) p.inner=∅:=by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨i,_,_⟩:=Finset.mem_biUnion.mp hx
    exact hempty.false i
  simpa only [hInt,Finset.sdiff_empty] using p.hAvoidReserve
end Oberwolfach
