module

public import Oberwolfach.OrdinaryPhysicalUnmarkedMatching
public import Oberwolfach.OrderedOrdinaryMatchedPartialEmbedding
public import Oberwolfach.LongRetainedPaddedIndexSet

@[expose] public section
/-! Extract the selected unmarked tuples at a hub and glue their assigned
factor components into one partial embedding on that same matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_physical_matched_partial_embedding
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (RM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (L:Finset (PhysicalSampledCandidate (mixedCandidateResources
      (ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W))) state))
    (u:U) (i₀:Fin K) (Cres:Finset (F u).ConnectedComponent)
    (assign:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u↪↥(Finset.univ\Cres))
    (hsize:∀a,Fintype.card (assign a).val=(a.val.val.1.getD i₀).val+1):
    let R:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π
    let payload:=ordinaryPhysicalUnmarkedPayload π d m RM state L u
    let components:=fun a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u=>(assign a).val;
    (∀x∈L,∀y∈L,x≠y→Disjoint (physicalSampledCandidateSet φ (mixedCandidateResources R) state x)
      (physicalSampledCandidateSet φ (mixedCandidateResources R) state y))→
    ∃g:∀a,components a↪Fin n,
      (∀a,Set.range (g a)=Set.range (payload a).2.1.val) ∧
      (∀a (x y:components a),(components a).toSimpleGraph.Adj x y↔
        (ordinaryWheelRim (orderedOrdinaryUniversalWheel (by have h:=long_padded_seed_exponent_positive (payload a).1;omega) (payload a).2)).Adj (g a x) (g a y)) ∧
    ∃ψ:{v:Fin n // ∃a,v∈(components a).supp}↪Fin n,
      ∀a (x:components a),ψ ⟨x.val,⟨a,x.property⟩⟩=g a x :=by
  intro R φ payload components hL
  have hC:Function.Injective components:=by
    intro a b h
    apply assign.injective
    exact Subtype.ext h
  let len:=fun a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u=>longPaddedSeedExponent (payload a).1+2
  let W:=fun a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u=>(payload a).2
  have hlen:∀a,3≤len a:=by intro a;have hh:=long_padded_seed_exponent_positive (payload a).1;dsimp [len];omega
  have hsize':∀a,Fintype.card (components a)=len a:=by
    intro a
    have hs:=hsize a
    rw [ordinary_physical_unmarked_payload_index π d m RM state L u a i₀] at hs
    change Fintype.card (components a)=(payload a).1.val+1 at hs
    have hthree:3≤Fintype.card (components a):=(component_regular_two_cycle_iso (F u) (hF u) (components a)).1
    have hreal:longPaddedSeedExponent (payload a).1+2=(payload a).1.val+1:=by
      rw [long_padded_seed_length_eq_exponent]
      exact long_assigned_padded_length_true (payload a).1 (by omega)
    dsimp [len]
    rw [hreal]
    exact hs
  have hhub:∀a,(W a).2=u:=fun a=>ordinary_physical_unmarked_payload_hub π d m RM state L u a
  have hdis:=ordinary_physical_unmarked_payload_matching π d m RM state L u hL
  have hh:=ordered_ordinary_matched_partial_embedding (F u) (hF u) π components hC len hlen W u hsize' hhub hdis
  convert hh using 1 <;> congr! 5
end Oberwolfach
