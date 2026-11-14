module

public import Oberwolfach.OrdinaryCorrectedStarProtectsDeeper

@[expose] public section
/-! Every wheel packed after the corrected star is reserved avoids the
    actual deeper induced pair in the original host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_corrected_star_packing_avoids_deeper
    (Q D F:SimpleGraph V) (H J:V→U→Prop) (I T:Finset V) (B W:Finset U) (r:ℕ)
    (hTI:T⊆I) (hWB:W⊆B)
    (hD:∀v∈T,∀w∈T,¬D.Adj v w)
    (hJ:∀v u,J v u→¬(v∈T∧u∈W)):
    let R:=ordinaryRimRootStar ((spanningRestriction Q I)\D) T;
    let S:=ordinarySpokeRootStar (fun v u=>(H v u∧v∈I∧u∈B)∧¬J v u) T W;
    let Qout:=Q\R;let Hout:=fun v u=>H v u∧¬S v u;
    ∀M:Finset (OrdinaryWheel Qout F Hout r),
      Disjoint (M.biUnion ordinaryWheelResources)
        (ordinaryHostResources (spanningRestriction Q T) (fun v u=>H v u∧v∈T∧u∈W)):=by
  intro R S Qout Hout M
  have hprotected:Disjoint (ordinaryHostResources Qout Hout)
      (ordinaryHostResources (spanningRestriction Q T) (fun v u=>H v u∧v∈T∧u∈W)):=
    (ordinary_corrected_star_protects_deeper Q D H J I T B W hTI hWB hD hJ).2.2
  apply hprotected.mono_left
  intro e he
  obtain ⟨A,hA,heA⟩:=Finset.mem_biUnion.mp he
  exact ((ordinaryWheelResources_subset_host A Qout Hout).mpr ⟨A.val.1.property,A.property.1⟩) heA
end Oberwolfach
