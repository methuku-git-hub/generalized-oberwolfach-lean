module

public import Oberwolfach.LongOrdinarySeedZeroAtHub
public import Oberwolfach.LongRawOrdinaryComponentAssignment

@[expose] public section
/-! Positive-support matching selects no ordinary wheel at a discarded
hub-length pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longDiscardedHubDecidableFin (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_discarded_hub_selected_zero
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (m d:ℕ) (θ D:ℝ)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (ni:Fin K→ℕ) (hni:∀i,1≤ni i)
    (w:∀i,OrdinaryCycle P (ni i+2)→ℝ)
    (wM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let ℓ:=fun i=>ni i+2
    let state:=typedMarkedResourceState (rawMarkedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j)
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let wO:=longAssignedOrdinarySeed F hF K m d θ D P π ni hni w
    let wmix:=longMixedSeedWeight wM wO
    let hub:=fun c:RestrictedResource (mixedCandidateResources R) e=>longRawSeedHub π d m ℓ c.val.1 c.val.2
    ∀(M:Finset (RestrictedResource (mixedCandidateResources R) e)) (i:Fin K) (u:U),
    (∀c∈M,0<mixedCandidateWeight wmix c.val) →
    longAssignedKeptFraction F hF K θ i u=0 →
    (M.filter (fun c=>c.val.1=some i ∧ hub c=u)).card=0 :=by
  intro ℓ state e R wO wmix hub M i u hpos hzero
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  obtain ⟨hcM,hidx,hhub⟩:=Finset.mem_filter.mp hc
  have hp:=hpos c hcM
  obtain ⟨⟨index,W⟩,hW⟩:=c
  cases index with
  | none=>simp at hidx
  | some q=>
    have hqi:q=i:=Option.some.inj hidx
    subst q
    have hWu:W.2=u:=by simpa only [hub,longRawSeedHub] using hhub
    have hz:longAssignedOrdinarySeed F hF K m d θ D P π ni hni w i W=0:=by
      apply long_ordinary_seed_zero_at_discarded_hub
      simpa only [hWu] using hzero
    simp only [wmix,longMixedSeedWeight,mixedCandidateWeight,wO] at hp
    rw [hz] at hp
    exact (lt_irrefl (0:ℝ)) hp
end Oberwolfach
