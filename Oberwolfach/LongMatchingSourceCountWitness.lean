module

public import Oberwolfach.LongRawPartialDomainClassCard
public import Oberwolfach.LongSelectedAlignedSourceWithLoad

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longMatchingSourceCountWitnessFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

def LongMatchingSourceCountWitness
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ) (θ eps:ℝ)
    (T:Finset (LongRawHubResource n U))
    (Nraw:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ))
      (Function.Embedding.subtype (·∈T)))):Prop:=
    let e:=Function.Embedding.subtype (·∈T)
    let A:=LongRawSelectedOrdinary π d m ℓ e Nraw
    let Q:=longRawSelectedOrdinaryWheel π d m ℓ e Nraw
    ∃assign:A↪(Σu,(F u).ConnectedComponent),
    ∃C:∀a:A,(F (Q a).val.2).ConnectedComponent,
      (∀a,(⟨(Q a).val.2,C a⟩:Σu,(F u).ConnectedComponent)=assign a) ∧
      (∀u,Fintype.card (longRawSourceDomain F π d m ℓ e Nraw C u)=
        ∑i:Fin K,(Nraw.filter (fun c=>c.val.1=some i ∧ longRawSeedHub π d m ℓ c.val.1 c.val.2=u)).card*ℓ i) ∧
      (∀u,|((Fintype.card (longRawSourceDomain F π d m ℓ e Nraw C u):ℕ):ℝ)-
        (1-θ)*(n:ℝ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i u)|≤
        ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ)))
end Oberwolfach
