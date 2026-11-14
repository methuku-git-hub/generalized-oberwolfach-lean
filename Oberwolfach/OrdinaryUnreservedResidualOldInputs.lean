module

public import Oberwolfach.OrdinaryUnreservedFactorPaths
public import Oberwolfach.ActualSumBufferedInteriorsDeleted
public import Oberwolfach.ActualPrescribedAvoidsDeletedInteriors

@[expose] public section
/-! The actual unreserved factors automatically provide the regularity,
selected-cycle, and restricted-old-domain inputs for residual placement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_unreserved_residual_restricted_old_inputs
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    {A B J:U→Type} [∀u,Fintype (A u)] [∀u,DecidableEq (A u)]
    [∀u,DecidableEq (B u)] [∀u,DecidableEq (J u)]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Cres:∀u,Finset (F u).ConnectedComponent) (c d:ℕ):
    let X:=fun u=>{x:Fin n // (F u).connectedComponentMk x∉Cres u}
    let H:=fun u=>(F u).induce {x | (F u).connectedComponentMk x∉Cres u};
    ∀(data:∀u,ActualResidualData (K:=A u⊕B u) (J:=J u) (H u))
      (ext:∀u,A u⊕B u→Fin (c*d+5)↪X u)
      (inner:∀u,A u→Fin (c*d+1)↪X u),
      (∀u,(data u).c=c)→(∀u,(data u).d=d)→
      (∀u,(data u).s₁=firstSumIndices)→
      (∀u i,((data u).P i).support=List.ofFn (ext u i))→
      (∀u i k,inner u i k=ext u (.inl i) ⟨k.val+2,by omega⟩)→
      (∀u,(data u).Cembed=(data u).t.biUnion (fun j=>((data u).C j).support.toFinset))→
      (∀u,(H u).IsRegularOfDegree 2) ∧
      (∀u,(data u).t.biUnion (fun j=>((data u).C j).support.toFinset)⊆(data u).Cembed) ∧
      (∀u,(data u).prescribed⊆(data u).oldDomain\bufferedPathStrictInterior (fun _:A u=>c*d) (inner u)):=by
  intro X H data ext inner hc hd hs hsupp hinner hC
  have hreg:∀u,(H u).IsRegularOfDegree 2:=fun u=>(ordinary_unreserved_factor_paths (F u) (hF u) (Cres u)).1
  refine ⟨hreg,?_,?_⟩
  · intro u
    rw [hC u]
  · intro u
    have hdis:=actual_sum_buffered_interiors_deleted_with_parameters (data u) c d (hc u) (hd u) (hs u) (ext u) (inner u) (hsupp u) (hinner u)
    exact actual_prescribed_subset_old_without_disjoint_interiors (data u) (hreg u) _ hdis
end Oberwolfach
