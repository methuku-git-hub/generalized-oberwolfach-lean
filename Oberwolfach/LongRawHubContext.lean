module

public import Oberwolfach.LongRawFamilyFintype
public import Oberwolfach.LongRawOrdinaryHubCount

@[expose] public section
/-! Named forms of the actual raw mixed state, resource family and fixed
weights, to expose the same sample and candidates in later applications. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

abbrev LongRawHubResource (n:ℕ) (U:Type):Type :=
  (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))

def longRawHubState (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):LongRawHubResource n U→Bool:=
  typedMarkedResourceState (rawMarkedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j)

def longRawHubCandidates (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ):Option (Fin K)→Type:=
  longRawSeedFamilies (U:=U) π d m ℓ

def longRawHubResources (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ):
    ∀i,longRawHubCandidates (U:=U) π d m ℓ i→Finset (LongRawHubResource n U):=
  longRawSeedResources π d m ℓ

def longRawHubNames (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ):
    ∀i,longRawHubCandidates (U:=U) π d m ℓ i→U:=longRawSeedHub π d m ℓ

instance longRawHubCandidatesFintype (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (i:Option (Fin K)):Fintype (longRawHubCandidates (U:=U) π d m ℓ i):=by
  dsimp [longRawHubCandidates]
  infer_instance

theorem long_raw_hub_context_spokes
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ) (i:Fin K) (u:U)
    (W:longRawHubCandidates (U:=U) π d m ℓ (some i)):
    (longRawHubResources (U:=U) π d m ℓ (some i) W∩ordinaryCommonHubSpokeRoots u).card=
      if longRawHubNames (U:=U) π d m ℓ (some i) W=u then ℓ i else 0 :=by
  convert long_raw_ordinary_hub_spoke_count π d m ℓ i u W using 1 <;>
    congr 3 <;> exact Subsingleton.elim _ _
end Oberwolfach
