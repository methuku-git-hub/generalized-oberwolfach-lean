module

public import Oberwolfach.LongRawSelectedOrdinaryMatching
public import Oberwolfach.LongDiscardedHubSelectedZero
public import Oberwolfach.LongPaddedAssignmentFromAbsoluteFrequency

@[expose] public section
/-! A positively weighted selected ordinary wheel belongs to a retained
hub--length pair; its padding is therefore its true prescribed length. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_padded_selected_ordinary_is_retained
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (m d:ℕ) (θ D:ℝ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (w:∀i,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (wM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let ni:=@longPaddedSeedExponent K
    let hni:=@long_padded_seed_exponent_positive K
    let ℓ:=fun i=>ni i+2
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let wO:=longAssignedOrdinarySeed F hF K m d θ D P π ni hni w
    let wmix:=longMixedSeedWeight wM wO
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
      (∀c∈M,0<mixedCandidateWeight wmix c.val)→
      ∀a:LongRawSelectedOrdinary π d m ℓ e M,
      θ/(100*(K:ℝ))≤longAssignedKeptFraction F hF K θ
        (longRawSelectedOrdinaryPayload π d m ℓ e M a).1
        (longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2 :=by
  intro ni hni ℓ state e R wO wmix M hpos a
  let i:Fin K:=(longRawSelectedOrdinaryPayload π d m ℓ e M a).1
  let u:U:=(longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2
  rcases long_kept_fraction_zero_or_retained F hF θ i u with hz|hr
  · have hcard:=long_discarded_hub_selected_zero F hF m d θ D P π ni hni w wM raw g j M i u hpos hz
    have hmem:a.val∈M.filter (fun c=>c.val.1=some i ∧ longRawSeedHub π d m ℓ c.val.1 c.val.2=u):=by
      apply Finset.mem_filter.mpr
      refine ⟨a.property.1,?_,?_⟩
      · exact (long_raw_selected_ordinary_index π d m ℓ e M a).symm
      · exact (long_raw_selected_ordinary_hub π d m ℓ e M a).symm
    have hp:0<(M.filter (fun c=>c.val.1=some i ∧ longRawSeedHub π d m ℓ c.val.1 c.val.2=u)).card:=
      Finset.card_pos.mpr ⟨a.val,hmem⟩
    have hcard' : (M.filter (fun c=>c.val.1=some i ∧ longRawSeedHub π d m ℓ c.val.1 c.val.2=u)).card=0 :=by
      convert hcard using 1 <;> congr 4 <;> exact Subsingleton.elim _ _
    omega
  · exact hr
end Oberwolfach
