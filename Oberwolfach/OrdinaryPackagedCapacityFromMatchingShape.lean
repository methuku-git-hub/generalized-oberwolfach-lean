module

public import Oberwolfach.CandidateOrdinaryFamilyCapacityForcedTargetsDirectReserve
public import Oberwolfach.OrdinaryMatchedPhysicalHubFamilyShape

@[expose] public section
/-! Size and forced-target capacity for the coherent packages extracted from
one physical matching. This shape retains all sampling and numerical inputs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryPackagedCapacityFromMatchingShape
    (m d:ℕ) (hm:7≤m) (hd:1≤d) (θ:ℝ) (hθ:0<θ) (err:ℝ) (herr:0<err):Prop :=
    ∃N:ℕ,∀{n K:ℕ} (hnN:N≤n) {U:Type} [Fintype U] [DecidableEq U] (hn:0<n) (hK:0<K)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (i₀:Fin K) (rsv:ℝ) (hrs0:0≤rsv) (hrs1:rsv≤1/100) (hθ1:θ≤1/100)
    (hClassReserve:OrdinaryClassReserveBound F hF i₀ rsv)
    (π:Equiv.Perm (Fin n)) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (ζ matchErr κ:ℝ)
    (hgood:RetainedRestrictionGood π d (fun e=>raw (Sum.inr e)) false t
      (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ Jret)
    (Cres:∀u,Finset (F u).ConnectedComponent)
    (hsize:∀u (c:↥(Cres u)),Fintype.card c.val=i₀.val+1)
    (hres:∀u,((i₀.val+1:ℕ):ℝ)*(Cres u).card=rsv*n)
    (hcounts:∀u (g:Bool),|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) u-
      (n:ℝ)*ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) u g/d|<(n:ℝ)^(3/4:ℝ)/d)
    (Rim:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop),
    let H:=rawMarkedPairSpokes π d raw true true
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState Rim H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state)),
    let AM:=fun u:U=>OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u
    let AU:=fun u:U=>OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u
    let len:=fun (u:U) (a:AU u)=>longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1+2
    let wheels:=fun (u:U) (a:AU u)=>(ordinaryPhysicalUnmarkedPayload π d m RM state L u a).2
    let E:={e:Fin n×Fin n // Rim (Sum.inl e)}
    let S:={e:Fin n×Fin n // Rim (Sum.inr e)}
    let MW:=MarkedWheel (fun e:E=>e.val.1) (fun e:E=>e.val.2) (fun e:S=>e.val.1) (fun e:S=>e.val.2) m π (3*d) (H false) (H true)
    let W:=fun u=>AM u→MW
    let Good:=fun u (w:W u)=>∀a,(w a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).1.val ∧ (w a).2.val=u
    let Pack:=fun u (w:W u)=>mixedWheelRimPack (len u) (Finset.univ.image w) (wheels u)
    let A:=fun u=>retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret u
    let B:=fun u=>{x:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (u,e))) x true}
    let root:=fun u=>retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t Jret u
    let Pos:=fun u (w:W u) (i:B u)=>packedPhysicalSpokePositions
      (fun e:E=>e.val.1) (fun e:E=>e.val.2) (fun e:S=>e.val.1) (fun e:S=>e.val.2)
      m (3*d) d π (H false) (H true) (Finset.univ.image w) u (root u (.inr i))
    let X:=fun u:U=>{x:Fin n | (F u).connectedComponentMk x∉Cres u}
    let G:=fun u=>(F u).induce (X u);
    ∀(Arc:Fin n→Fin n→Prop) (Avail Reserve:U→Finset (Fin n))
    (p:∀u,OrdinaryMatchedResidualHubPackage (G u) m d π (root u) Arc (Avail u) (Reserve u)
      (Good u) (Pack u) (Pos u) (len u)),
    let Q:=physicalSampledCandidateSet φ (mixedCandidateResources RR) state
    let Row:=fun u=>physicalSampledRow φ state (ordinaryPhysicalRow (.inr (.inr u)));
      (∀u,(1-θ-matchErr)*(n:ℝ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i)≤
        ((∑j:AU u,len u j):ℝ))→
      (∀u,(∑g:Bool,ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) u g)≤1/8)→
      0≤ζ→0≤matchErr→
      1/(8*(d:ℝ))+((m:ℝ)+1)*(d:ℝ)*ζ+matchErr≤err/2→
      (∀u,((Row u\L.biUnion Q).card:ℝ)≤κ*n)→
      ∀δ:ℝ,2*θ+err+((m:ℝ)+2)*κ≤δ→
      ∀errUpper:ℝ,0≤errUpper→errUpper≤θ/8→
      (∀u,((∑j:AU u,len u j):ℝ)≤
        (1-θ+errUpper)*(n:ℝ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i))→
      ∀(αCap b z:ℝ),0<αCap→0≤b→16/(d:ℝ)+16*κ+16*b/αCap+4*z≤θ/8→
      ∀(Gbad:SimpleGraph (Fin n)) (Z:Finset (Fin n)),(∀v,(Gbad.degree v:ℝ)≤b*n)→(Z.card:ℝ)≤z*n→
      ∀u,(Fintype.card {x // x∈(p u).data.remaining}:ℝ)≤δ*n ∧
      8*(residualSubtypeSet (p u).data.remaining (p u).data.prescribed).card+
        8*⌈4*(Gbad.edgeFinset.card:ℝ)/(αCap*n)⌉₊+4*Z.card+10≤Fintype.card {x // x∈(p u).data.remaining}
end Oberwolfach
