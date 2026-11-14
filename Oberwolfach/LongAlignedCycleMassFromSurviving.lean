module

public import Oberwolfach.LongResidualCycleMatchingMass
public import Oberwolfach.LongSurvivingMatchingMass
public import Oberwolfach.LongMatchingMassFromLiftedSource

@[expose] public section
/-! The aligned cycles use exactly the ordinary mass of the surviving matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K : ℕ} {U L : Type} [Fintype U] [DecidableEq U] [DecidableEq L]

local instance selectedOrdinaryFinite {X:Type} [Fintype X] [DecidableEq X]
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ) (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e)):
    Fintype (LongRawSelectedOrdinary π d m ℓ e M):=by
  let f:(LongRawSelectedOrdinary π d m ℓ e M)→M:=fun a=>⟨a.val,a.property.1⟩
  have hf:Function.Injective f:=by intro a b h;apply Subtype.ext;exact congrArg (fun x:M=>x.val) h
  exact Fintype.ofInjective f hf

theorem long_aligned_cycle_mass_from_surviving_matching
    (F:U→SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (S T:Finset (LongRawHubResource n U)) (hST:S⊆T)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ))
      (Function.Embedding.subtype (·∈S)))) :
    let e:=Function.Embedding.subtype (·∈T)
    let q:=survivingCandidateEmbedding (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) S T hST
    let N:=M.map q
    ∀(hmaps:LongRawOrdinaryComponentMapsProperty F π d m ℓ e N)
    (assign:LongRawSelectedOrdinary π d m ℓ e N↪(Σu,(F u).ConnectedComponent))
    (hhub:∀a,(assign a).1=(longRawSelectedOrdinaryWheel π d m ℓ e N a).val.2)
    (w:U) (data:ActualResidualData (K:=L) (J:={a:LongRawSelectedOrdinary π d m ℓ e N // (assign a).1=w}) (F w))
    (ht:data.t=Finset.univ)
    (hEmbed:data.Cembed=data.t.biUnion (fun j=>(data.C j).support.toFinset))
    (hlen:∀j,(data.C j).length=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e N j.val).1),
    data.Cembed.card=∑i:Fin K,(M.filter (fun c=>c.val.1=some i ∧
      longRawSeedHub π d m ℓ c.val.1 c.val.2=w)).card*ℓ i:=by
  intro e q N hmaps assign hhub w data ht hEmbed hlen
  have hc:=long_residual_cycle_mass_eq_matching_counts (L:=L) F π d m ℓ e N hmaps assign hhub w data ht hEmbed hlen
  apply hc.trans
  apply Finset.sum_congr rfl
  intro i hi
  rw [long_surviving_matching_count_preserved π d m ℓ S T hST M i w]

theorem long_aligned_cycle_mass_estimate_from_same_matching
    (F:U→SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (S T:Finset (LongRawHubResource n U)) (hST:S⊆T)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ))
      (Function.Embedding.subtype (·∈S)))) :
    let e:=Function.Embedding.subtype (·∈T)
    let q:=survivingCandidateEmbedding (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) S T hST
    let N:=M.map q
    ∀(hmaps:LongRawOrdinaryComponentMapsProperty F π d m ℓ e N)
    (assign:LongRawSelectedOrdinary π d m ℓ e N↪(Σu,(F u).ConnectedComponent))
    (hhub:∀a,(assign a).1=(longRawSelectedOrdinaryWheel π d m ℓ e N a).val.2)
    (w:U) (data:ActualResidualData (K:=L) (J:={a:LongRawSelectedOrdinary π d m ℓ e N // (assign a).1=w}) (F w))
    (ht:data.t=Finset.univ)
    (hEmbed:data.Cembed=data.t.biUnion (fun j=>(data.C j).support.toFinset))
    (hlen:∀j,(data.C j).length=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e N j.val).1)
    (sourceCard:ℕ) (target err:ℝ)
    (hcount:sourceCard=∑i:Fin K,(N.filter (fun c=>c.val.1=some i ∧
      longRawSeedHub π d m ℓ c.val.1 c.val.2=w)).card*ℓ i)
    (hsource:|(sourceCard:ℝ)-target|≤err),
    |(data.Cembed.card:ℝ)-target|≤err:=by
  intro e q N hmaps assign hhub w data ht hEmbed hlen sourceCard target err hcount hsource
  have hc:=long_aligned_cycle_mass_from_surviving_matching F π d m ℓ S T hST M hmaps assign hhub w data ht hEmbed hlen
  rw [hc]
  exact long_matching_mass_from_lifted_source π d m ℓ S T hST M w sourceCard target err hcount hsource
end Oberwolfach
