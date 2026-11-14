module

public import Oberwolfach.LongActualResidualMassLower
public import Oberwolfach.ActualResidualFullMassBound
public import Oberwolfach.LongActualResidualMissingBound
public import Oberwolfach.ResidualLongErrorBudget
public import Oberwolfach.ResidualOrdinaryMassFromSource
public import Oberwolfach.LongActualResidualSizeAtTolerance
public import Oberwolfach.LongResidualCycleMatchingMass
public import Oberwolfach.LongActualResidualSizeFromSource
public import Oberwolfach.LongActualResidualSizeLower
public import Oberwolfach.ResidualOrdinaryMassFromSourceUpper
public import Oberwolfach.LongMissingErrorBudget

@[expose] public section
/-! The actual residual has at most 10θn vertices once the same sample's
start, retention, ordinary-mass and matching tests hold. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longResidualBothBoundsSelectedFinite {n K:ℕ} {U X:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ) (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e)):
    Fintype (LongRawSelectedOrdinary π d m ℓ e M):=by
  let f:(LongRawSelectedOrdinary π d m ℓ e M)→M:=fun a=>⟨a.val,a.property.1⟩
  have hf:Function.Injective f:=by intro a b h;apply Subtype.ext;exact congrArg (fun x:M=>x.val) h
  exact Fintype.ofInjective f hf

theorem long_actual_residual_bounds_from_matching_source
    (m d:ℕ) (hm:0<m) (hd:m+2≤d) (θ:ℝ) (hθ:0<θ) (hθmax:θ≤1/100)
    (ζ:ℝ) (N:ℕ)
    (hN:∀n:ℕ,N≤n→∀q errOrd:ℝ,
      q≤1/((m:ℝ)+1)→errOrd≤θ*n→
      (n:ℝ)*q/d+(((m+1)*d-1:ℕ):ℝ)*(2*((n:ℝ)^(3/4:ℝ)/d)+ζ*n)+errOrd≤4*θ*n):
    ∀(n K:ℕ) (hn:N≤n) (hn0:0<n) (hK:0<K)
    (U:Type) [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (ℓ:Fin K→ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (hgood:RetainedRestrictionGood π d (fun e=>raw (Sum.inr e)) false t
      (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ Jret)
    (Del:Finset (Sym2 (Fin n))),
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let S:=longRawSurvivingResources P π d raw true true Del
    let hST:=long_raw_surviving_resources_subset P π d raw true true Del
    let q:=survivingCandidateEmbedding R S T hST
    let Q:=restrictedResourceSet R (Function.Embedding.subtype (·∈S))
    ∀(M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S)))) (w:U)
    (lam α γ errOrd:ℝ) (hlam:0≤lam) (hlamθ:lam≤θ) (hα:α≤lam/(10*(d:ℝ)))
    (hγ:0≤γ) (hγcap:γ≤lam/(10*(d:ℝ)))
    (hmatch:∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (α*n) (γ*(longRawIncidenceSet S i).card))
    (herrOrd:errOrd≤θ*n)
    (hcounts:∀g:Bool,|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) w-
      (n:ℝ)*longAssignedIntervalProbability F hF K m θ w g/d|<(n:ℝ)^(3/4:ℝ)/d),
    ∀(hmaps:LongRawOrdinaryComponentMapsProperty F π d m ℓ (Function.Embedding.subtype (·∈S)) M)
    (assign:LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (·∈S)) M↪(Σu,(F u).ConnectedComponent))
    (hhub:∀a,(assign a).1=(longRawSelectedOrdinaryWheel π d m ℓ (Function.Embedding.subtype (·∈S)) M a).val.2),
    let A:=retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w
    let B:={x:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) x true}
    let Marked:=longRawMarkedWheelsAtHub P π d m ℓ raw true true (M.map q) w
    letI : DecidableEq (A⊕B) := Classical.decEq _
    ∀(a:ActualResidualData (K:=A⊕B) (J:={z:LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (·∈S)) M // (assign z).1=w}) (F w))
    (hc:a.c=m+1) (hd':a.d=d) (hs₁:a.s₁=firstSumIndices) (hs₂:a.s₂=secondSumIndices)
    (hpositions:∀b:B,a.T (.inr b)=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π
      (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true) Marked w b.val)
    (hEmbed:a.Cembed=a.t.biUnion (fun j=>(a.C j).support.toFinset))
    (ht:a.t=Finset.univ)
    (hlen:∀j,(a.C j).length=ℓ (longRawSelectedOrdinaryPayload π d m ℓ (Function.Embedding.subtype (·∈S)) M j.val).1)
    (sourceMass:ℕ)
    (hcount:sourceMass=∑i:Fin K,(M.filter (fun c=>c.val.1=some i ∧
      longRawSeedHub π d m ℓ c.val.1 c.val.2=w)).card*ℓ i)
    (hsource:|((sourceMass:ℝ)-(n:ℝ)*((1-θ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i w)))|≤errOrd),
    θ*n-errOrd-2*((m:ℝ)+1)*(n:ℝ)^(3/4:ℝ)≤(a.remaining.card:ℝ) ∧
    (a.remaining.card:ℝ)≤10*θ*n:=by
  intro n K hn hn0 hK U _ _ F hF P π hnoshort ℓ raw t Jret hgood Del R T S hST q Q M w lam α γ errOrd hlam hlamθ hα hγ hγcap hmatch herrOrd hcounts hmaps assign hhub A B Marked a hc hd' hs₁ hs₂ hpositions hEmbed ht hlen sourceMass hcount hsource
  letI : DecidableEq (A⊕B) := Classical.decEq _
  have hth :=long_residual_cycle_mass_eq_matching_counts (L:=A⊕B) F π d m ℓ (Function.Embedding.subtype (·∈S)) M hmaps assign hhub w
  have hc' :=hth a ht hEmbed hlen
  have hcount' : (∑i:Fin K,(M.filter (fun c=>c.val.1=some i ∧
      longRawSeedHub π d m ℓ c.val.1 c.val.2=w)).card*ℓ i)=sourceMass := hcount.symm
  have hcard:a.Cembed.card=sourceMass:=hc'.trans hcount'
  have hCupper:=residual_ordinary_mass_upper_from_source_count a hEmbed sourceMass hcard
    ((n:ℝ)*((1-θ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i w))) errOrd hsource
  have hd0:0<d:=lt_of_lt_of_le (by omega : 0<m+2) hd
  have hθ1:θ≤1:=by linarith only [hθmax]
  have hLower:=long_actual_residual_size_lower_from_counts (n:=n) (K:=K) (U:=U)
    (J:={z:LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (·∈S)) M // (assign z).1=w}) hn0 m d hm hd0 F hF π
    (fun e=>raw (Sum.inr e)) t Jret w a hc hd' hs₁ hs₂ θ ((n:ℝ)^(3/4:ℝ)) errOrd hθ1 hcounts hCupper
  refine ⟨hLower,?_⟩
  clear hLower hCupper hc' hth hcount' ht hlen hcount hmaps hhub
  revert n
  intro n
  have hdec : instDecidableEqFin n = longActualResidualSizeSourceMassFin n := Subsingleton.elim _ _
  rw [hdec]
  letI : DecidableEq (Fin n) := longActualResidualSizeSourceMassFin n
  simp only []
  intro hn hn0 F hF P π hnoshort raw Jret hgood Del M hmatch herrOrd hcounts assign
  let A:=retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w
  let B:={x:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) x true}
  have hsum : Classical.decEq (A⊕B) = @instDecidableEqSum A B _ _ := Subsingleton.elim _ _
  try rw [hsum]
  intro a hc hd' hs₁ hs₂ hpositions hEmbed hsource hcard
  exact long_actual_residual_size_from_source_mass m d hm hd θ hθ hθmax ζ N hN n K hn hn0 hK U F hF P π hnoshort ℓ raw t Jret hgood Del M w lam α γ errOrd hlam hlamθ hα hγ hγcap hmatch herrOrd hcounts a hc hd' hs₁ hs₂ hpositions hEmbed sourceMass hcard hsource
end Oberwolfach
