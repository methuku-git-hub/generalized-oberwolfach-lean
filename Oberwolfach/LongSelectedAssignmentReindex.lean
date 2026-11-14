module

public import Oberwolfach.LongPaddedSelectedRetained
public import Oberwolfach.LongPaddedAssignmentFromAbsoluteFrequency

@[expose] public section
/-! Convert the existing selected-candidate component assignment to the
extracted ordinary-wheel indexing, preserving both hub and true length. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longSelectedAssignmentDecidableFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_padded_selected_assignment_reindex
    (hK:0<K) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (m d:ℕ) (θ D:ℝ) (hθ:0<θ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
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
    let hub:=fun c:RestrictedResource (mixedCandidateResources R) e=>longRawSeedHub π d m ℓ c.val.1 c.val.2
    let idx:=fun c:RestrictedResource (mixedCandidateResources R) e=>c.val.1.getD ⟨0,hK⟩
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
      (∀c∈M,0<mixedCandidateWeight wmix c.val) →
    ∀h:{c // c∈M.filter (fun c=>c.val.1.isSome)}↪(Σu,(F u).ConnectedComponent),
      (∀c,(h c).1=hub c.val ∧ Fintype.card (h c).2=(idx c.val).val+1) →
    ∃assign:LongRawSelectedOrdinary π d m ℓ e M↪(Σu,(F u).ConnectedComponent),
      (∀a,(assign a).1=(longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2) ∧
      (∀a,Fintype.card (assign a).2=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a).1) :=by
  intro ni hni ℓ state e R wO wmix hub idx M hpos h hh
  let reindex:LongRawSelectedOrdinary π d m ℓ e M↪{c // c∈M.filter (fun c=>c.val.1.isSome)}:=
    ⟨fun a=>⟨a.val,Finset.mem_filter.mpr a.property⟩,by
      intro a b hab
      apply Subtype.ext
      have hx:=congrArg (fun z:{c // c∈M.filter (fun c=>c.val.1.isSome)}=>z.val) hab
      exact hx⟩
  let assign:LongRawSelectedOrdinary π d m ℓ e M↪(Σu,(F u).ConnectedComponent):=
    ⟨fun a=>h (reindex a),fun a b hab=>reindex.injective (h.injective hab)⟩
  refine ⟨assign,?_,?_⟩
  · intro a
    have hs:=(hh (reindex a)).1
    have he:=long_raw_selected_ordinary_hub π d m ℓ e M a
    exact hs.trans he.symm
  · intro a
    have hs:=(hh (reindex a)).2
    have he:=long_raw_selected_ordinary_index π d m ℓ e M a
    have hi:idx a.val=(longRawSelectedOrdinaryPayload π d m ℓ e M a).1:=by
      dsimp only [idx]
      rw [←he]
      rfl
    have hr:=long_padded_selected_ordinary_is_retained F hF m d θ D P π w wM raw g j M hpos a
    have hl:=long_retained_hub_padded_length_exact F hF θ hθ _ _ hr
    dsimp only [assign] at *
    change Fintype.card (h (reindex a)).2=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a).1
    have hl':ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a).1=
        (longRawSelectedOrdinaryPayload π d m ℓ e M a).1.val+1:=by
      change longPaddedSeedExponent (longRawSelectedOrdinaryPayload π d m ℓ e M a).1+2=_
      exact hl
    rw [hl']
    change Fintype.card (h (reindex a)).2=(idx a.val).val+1 at hs
    simpa only [hi] using hs
end Oberwolfach
