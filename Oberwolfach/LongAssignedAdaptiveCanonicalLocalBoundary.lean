module

public import Oberwolfach.RetainedBoundaryHubsThreshold
public import Oberwolfach.RetainedAbsorberOccurrenceThreshold
public import Oberwolfach.LongAssignedIntervalProbabilityUpper
public import Oberwolfach.RetainedUnassignedColumnThreshold
public import Oberwolfach.RetainedUnassignedHubThreshold
public import Oberwolfach.FiniteLawIntersectionLower
public import Oberwolfach.LongAssignedReferenceInnerDomainsLocalFamily
public import Oberwolfach.LongAssignedReferenceInnerDomainsRimRow
public import Oberwolfach.LongAssignedReferenceInnerDomains
public import Oberwolfach.LongAssignedReferenceMatchingStartsPathTests
public import Oberwolfach.LongAssignedReferenceMatchingStartsNeighbourTests
public import Oberwolfach.LongAssignedReferenceMatchingWithStarts
public import Oberwolfach.LongAssignedReferenceManuscriptPartials
public import Oberwolfach.MarkedAdaptiveAgreementAssignedProbability
public import Oberwolfach.MarkedRetainedReservoirSelection
public import Oberwolfach.MarkedVortexFixedSelectionProperty
public import Oberwolfach.MarkedAdaptiveReferenceMass
public import Oberwolfach.MarkedAdaptiveLevelBalances
public import Oberwolfach.MarkedAdaptiveCanonicalCentres

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
theorem long_assigned_full_adaptive_fixed_selection_canonical_with_local_rim_hub_column_absorber_boundary_families
    (r k₀ Qpow:ℕ) (hr:2≤r) (hQpow:0<Qpow) (hlen:r+4+1=(k₀+2)*2)
    (αRef sstar ω γRich tstar kstar κ:ℝ)
    (hαRef:0<αRef) (hsstar:0<sstar) (hsstar1:sstar≤1/100) (hω:0<ω)
    (hmargin:successorCycleRatio k₀+αRef/2≤1/2+αRef)
    (hγRich:0<γRich) (hγRich1:γRich≤1/2) (htstar:0<tstar) (htstar1:tstar≤1)
    (horder:tstar≤sstar) (hkstar:0<kstar) (hκ:0<κ)
    (K d:ℕ) (hK3:3≤K) (hm:7≤(r+4)) (hd:2≤d)
    (θ ρ₀ BM:ℝ) (hθpos:0<θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hBM:0<BM) (hωBound:4*ω≤ρ₀)
    (hspace:1/(8*(d:ℝ))≤θ/2)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (ζret:ℝ) (hζret:0<ζret)
    (alpha γ ε₀ eps lam:ℝ) (hε₀:ε₀<1) (heps:0<eps) (heps1:eps≤1) (hγε:γ≤eps) (hlam:0≤lam) (hlamθ:lam≤θ) (hepsAssign:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (halpha:0<alpha) (halphaMass:alpha≤θ/(200*(K:ℝ)*(K:ℝ))) (hγ:0<γ):
    let ni:=@longPaddedSeedExponent K
    let hni:=@long_padded_seed_exponent_positive K
    let hpadded:=@long_padded_seed_length_eq_exponent K
    let pstar₀:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*((((r+4):ℕ):ℝ)+1))))
    let BMseed₀:=2*BM/pstar₀^(2*(r+4)+1)
    let BOseed₀:=fun i=>2*BO i/pstar₀^(2*(ni i+2))
    let Kpair₀:=1+((((r+4):ℕ):ℝ)+1)^4*BMseed₀+∑i:Fin K,((ni i:ℝ)+2)^3*BOseed₀ i
    let C₀:=10*(((((r+4):ℕ):ℝ)+1)^4*BMseed₀+∑i:Fin K,((ni i:ℝ)+2)^4*BOseed₀ i)
    ∃ β βCommon εAbs εRob ζRob δAbs:ℝ,0<β∧0<βCommon∧0<εAbs∧0<εRob∧0<ζRob∧0<δAbs ∧
    ∀(εRef δRef ηRich χ χCommon Csize Qreal pstarRef ζ εBal Kbal ζBal χBal εNbr Knbr ζNbr χNbr Bload εLoad Kload ζLoad χLoad ζLocal χLocal ζConfig χConfig:ℝ)
    (hεRef:0<εRef) (hδRef:0<δRef) (hηRich:0<ηRich) (hηRich1:ηRich<1) (hχ:0<χ)
    (hχCommon:0<χCommon) (hpstarRef:0<pstarRef) (hζ:0<ζ) (hεBal:0<εBal) (hKbal:1≤Kbal) (hζBal:0<ζBal) (hχBal:0<χBal)
    (hεNbr:0<εNbr) (hKnbr:1≤Knbr) (hζNbr:0<ζNbr) (hχNbr:0<χNbr) (hBload:0<Bload) (hεLoad:0<εLoad)
    (hKload:1≤Kload) (hζLoad:0<ζLoad) (hχLoad:0<χLoad) (hζLocal:0<ζLocal) (hχLocal:0<χLocal) (hζConfig:0<ζConfig) (hχConfig:0<χConfig)
    (hQreal:0<Qreal) (hNbr:ℕ) (hpstarBound:4*(((r+4):ℕ):ℝ)*pstarRef≤ρ₀*(1/100)) (hgap:χ+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig<ε₀),
    ∀ (Cscale δrow δhub δcol δocc δbd:ℝ) (hCscale:0≤Cscale) (hδrow:0<δrow) (hδbound:δrow≤(1-ε₀)/512)
      (hδhub:0<δhub) (hδcol:0<δcol) (hδocc:0<δocc) (hδbd:0<δbd)
      (hδhubgap:δhub+δcol+δocc+δbd≤(ε₀-(χ+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig))/2),
    ∃MLevel:ℕ,1≤MLevel ∧
    ∃η:ℝ,0<η ∧ ∃t₀ τ₀ Δ ξ:ℝ,0<t₀ ∧ 0<τ₀ ∧ τ₀≤1/16 ∧ 0<Δ ∧ 0<ξ ∧ 4*ξ≤eps/2 ∧ ∃N:ℕ,
    ∀size:ℕ,∃a₀ b₀ e₀ aRob bRob eRob:ℕ,∀f₀:ℕ,∃NHost:ℕ,
    ∀n:ℕ,∀hn:max (max N NHost) 1≤n,∀(U:Type) [Fintype U] [DecidableEq U],
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (ρ D:ℝ) (hρlo:ρ₀≤ρ) (hρ1:ρ≤1) (hD:0<D)
    (hsize:ρ*D=2*Fintype.card U) (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (τ A:ℝ) (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A BM weight)
    (hDlo:(n:ℝ)/2≤D) (hDhi:D≤2*n)
    (w:∀i,OrdinaryCycle P (ni i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(ni i))
    (huv:Fintype.card U≤n)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (vertices:Finset (Fin n)) (Ilevel:Type) (Tlevel:Finset Ilevel)
    (Alevel Blevel:Ilevel→Finset (Fin n)) (Hlevel:Ilevel→Finset U)
    (hminCol:∀i∈Tlevel,retainedUnassignedColumnThreshold d hd δcol hδcol≤(Alevel i).card)
    (hminOcc:∀i∈Tlevel,retainedAbsorberOccurrenceThreshold d hd δocc hδocc≤(Alevel i).card)
    (hminBd:∀i∈Tlevel,retainedBoundaryHubsThreshold d hd δbd hδbd≤(Alevel i).card)
    (hJpos:∀i∈Tlevel,0<(Hlevel i).card) (hJA:∀i∈Tlevel,(Hlevel i).card≤(Alevel i).card)
    (hminHub:∀i∈Tlevel,retainedUnassignedHubThreshold d hd (1/2) δhub (by norm_num) hδhub≤(Alevel i).card)
    (hHlevel:∀i∈Tlevel,((Hlevel i).card:ℝ)≤(1/2:ℝ)*(Alevel i).card)
    (hmin:∀i∈Tlevel,localRowBudgetThreshold Cscale δrow hCscale hδrow≤(Alevel i).card)
    (hinjLevel:Set.InjOn (fun i=>(Alevel i).card) Tlevel)
    (hBlevel:∀i∈Tlevel,((Blevel i).card:ℝ)≤Cscale*(Alevel i).card)
    (εHost:ℝ)
    (he:∀i∈longRetainedSeedIndices F hF K θ,∀x y,
      (∑C:OrdinaryCycle P (ni i+2),if C.val.val.Adj x y then w i C else 0)=if P.Adj x y then 1 else 0)
    (hdeg:∀x,|(P.degree x:ℝ)-D|≤εHost*n)
    (hbudgetV:∀i∈longRetainedSeedIndices F hF K θ,
      6*((ni i+2:ℕ):ℝ)^4*BO i*(2*(3*d))+εHost*n≤τ*D)
    (hbudgetE:∀i∈longRetainedSeedIndices F hF K θ,
      5*((ni i+2:ℕ):ℝ)^4*BO i*(2*(3*d))/n≤τ)
    (hτnonneg:0≤τ) (hτbound:τ≤τ₀),
    ∀ (W Z Hdom:ℕ→Type)
      [∀ i,Fintype (W i)] [∀ i,Fintype (Z i)] [∀ i,LinearOrder (W i)] [∀ i,DecidableEq (Z i)]
      [∀ i,Fintype (Hdom i)] [∀ i,DecidableEq (Hdom i)],
    εHost≤δAbs → (∀v,(1/2+αRef)*n≤(P.degree v:ℝ)) →
    ∀ (fV:∀ i,W i↪o(Fin n)) (gV:∀ i,Z i↪U) (ρi:∀ i,Equiv.Perm (W i)),
      (∀ i x,fV i (ρi i x)=π (fV i x)) →
    ∀ L:ℕ,(L+1:ℝ)≤(Fintype.card (Fin n):ℝ)^Csize →
      (∀ i≤L,MLevel≤Fintype.card (W i)) → (∀ i≤L,MLevel≤Fintype.card (Z i)) →
      (∀ i<L,(Fintype.card (W (i+1)):ℝ)≤ηRich*Fintype.card (W i)) →
      (∀ i≤L,κ*Fintype.card (W i)≤(Fintype.card (Z i):ℝ)) →
      (∀ i≤L,Fintype.card (Z i)≤Fintype.card (W i)) →
      (∀ i≤L,(Fintype.card (Z i):ℝ)≤Kload*Fintype.card (W i)) →
      (∀ i≤L,Fintype.card (Hdom i)≤Fintype.card (W i)) →
    ∀ (Aset:∀ i,Finset (W i)) (Bset:∀ i,Finset (Z i)) (Scale:ℕ→ℕ),
      (∀ i≤L,MLevel≤(Aset i).card) → (∀ i≤L,MLevel≤(Bset i).card) →
      (∀ i<L,(Scale (i+1):ℝ)≤ηRich*Scale i) →
      (∀ i≤L,(Aset i).card≤Scale i) → (∀ i≤L,(Bset i).card≤Scale i) →
      (∀ i≤L,∀ x,ρi i x∈Aset i ↔ x∈Aset i) →
      (∀ i≤L,(Fintype.card (W i):ℝ)≤Kbal*Scale i) →
      (∀ i≤L,(Fintype.card (Z i):ℝ)≤Kbal*Scale i) →
      (∀ i<L,((Aset (i+1)).card:ℝ)≤ηRich*(Aset i).card) →
      (∀ i<L,((Bset (i+1)).card:ℝ)≤ηRich*(Bset i).card) →
      (∀ i≤L,(Fintype.card (W i):ℝ)≤Knbr*(Aset i).card) →
      (∀ i≤L,(Fintype.card (Z i):ℝ)≤Knbr*(Aset i).card) →
      (∀ i≤L,(Fintype.card (W i):ℝ)≤Knbr*(Bset i).card) →
      (∀ i≤L,∀ x:W i,(1/2+γRich)*(Aset i).card≤(((P.comap (fV i)).neighborFinset x∩Aset i).card:ℝ)) →
    let Dbal:=fun i=>2*((Bset i).card:ℝ)/ρ
    ∀ (δPbal:ℝ),0≤δPbal → δPbal≤εBal/4 →
      (∀ i≤L,∀ x:W i,|(((P.comap (fV i)).neighborFinset x∩Aset i).card:ℝ)-Dbal i|≤δPbal*Scale i) →
    ∀ (Dlevel:ℕ→ℝ) (δP:ℝ),0≤δP → δP≤εRef/4 →
      (∀ i≤L,∀ x:W i,|((P.comap (fV i)).degree x:ℝ)-Dlevel i|≤δP*Fintype.card (W i)) →
      (∀ i≤L,∀ x:W i,(1/2+γRich)*Fintype.card (W i)≤((P.comap (fV i)).degree x:ℝ)) →
    ∀ (bdom:∀ i,Hdom i↪Z i),
    let Dload:=fun i=>2*(Fintype.card (Hdom i):ℝ)/ρ
    ∀ (τLevel Aload:ℝ) (levelWeight:∀ i,(Fin ((r+4)+1)→W i)→ℝ),
      (∀ i≤L,(Fintype.card (W i):ℝ)/2≤Dload i) →
      (∀ i≤L,Dload i≤2*Fintype.card (W i)) →
      (∀ i≤L,SuccessorSequenceWeightConditions (P.comap (fV i)) (ρi i) (3*d) (Dload i) τLevel Aload Bload (levelWeight i)) →
    kstar≤ρ*(1/100)/2 → kstar≤ρ*((1/100)/(((r+4):ℕ):ℝ))/2 → tstar≤(1/100)/(((r+4):ℕ):ℝ) →
    let t:=t₀
    let tHub:=ξ*(n:ℝ)
    let b:=longAssignedApproxOrdinaryWeight F hF K (r+4) θ
    let a:=longAssignedApproxMarkedWeight F hF K (r+4) θ
    let p₁:=ρ*(1/100)/2
    let k₁:=ρ*((1/100)/(((r+4):ℕ):ℝ))/2
    let p₂:=(∑u,b u)/D
    let k₂:=(∑u,a u)/D
    let udens:=2*(∑u,(1-1/100-(1/100)/(((r+4):ℕ):ℝ)-a u-b u))/D
    let q:=longAssignedIntervalProbability F hF K (r+4) θ
    let s:=longAssignedSpokeProbability F hF K (r+4) θ
    let hLaw:=long_assigned_actual_raw_law_parameters (by omega) F hF Allowed hAllowed K (by omega) (r+4) d hm hd θ ρ₀ ρ D
      hθpos.le hθ hρ₀ hρlo hρ1 hD hsize hcut hclass
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p₁ k₁ p₂ k₂ udens
      hLaw.1 hLaw.2.1 hLaw.2.2.1 hLaw.2.2.2.1 hLaw.2.2.2.2.1 hLaw.2.2.2.2.2.1
      d hd q hLaw.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.1 s
      hLaw.2.2.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.2.2)
    let f:=fun (ω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) e=>
      rawExpandedMarkedCollapse e (ω e)
    let pstar:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*((((r+4):ℕ):ℝ)+1))))
    let BMseed:=2*BM/pstar^(2*(r+4)+1)
    let BOseed:=fun i=>2*BO i/pstar^(2*(ni i+2))
    let Wm:=longAssignedMarkedSeed F hF K (r+4) d θ D π weight
    let Wo:=longAssignedOrdinarySeed F hF K (r+4) d θ D P π ni hni w
    let C:=10*(((((r+4):ℕ):ℝ)+1)^4*BMseed+∑i:Fin K,((ni i:ℝ)+2)^4*BOseed i)
    let ℓ:=fun i=>ni i+2
    let Wmix:=longMixedSeedWeight Wm Wo
    let R:=longRawHubResources (U:=U) π d (r+4) ℓ
    let Pair:Option (Fin K)→ℝ:=fun i=>match i with
      | none=>((((r+4):ℕ):ℝ)+1)^4*BMseed
      | some i=>((ni i:ℝ)+2)^3*BOseed i
    let Kpair:=1+((((r+4):ℕ):ℝ)+1)^4*BMseed+∑i:Fin K,((ni i:ℝ)+2)^3*BOseed i
    let failure:=4*(Fintype.card U:ℝ)*Real.exp (-2*tHub^2/((4*(d:ℝ)+3)^2*(n:ℝ)))
    letI : Nonempty (Fin n):=⟨⟨0,by omega⟩⟩
    let Ret:=fun raw:RawMarkedOutcome (Fin n) U Bool Bool=>
      StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
        (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false))
    let ν:=fun raw:RawMarkedOutcome (Fin n) U Bool Bool=>
      startRetentionLaw (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
        (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)) (startRetentionMinimum_le _)
    let Prior:=MarkedAdaptiveAgreementProperty r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
      β βCommon εAbs εRob ζRob εRef δRef γRich p₁ k₁ (1/100) tstar ζ εBal ζBal εNbr ζNbr Bload εLoad Kload ζLoad ζLocal ζConfig ρ₀ sstar kstar τLevel
      P π fV gV ρi Aset Bset Scale Dlevel Dload bdom levelWeight q s false false
    ∃z:(Σω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,Ret (f ω)),
      0<(μ.sigma (fun ω=>ν (f ω))).mass z ∧ Prior ⟨f z.1,z.2⟩ ∧
        (∀x,|(((P.neighborFinset x∩vertices).filter (fun y=>(z.1 (Sum.inl s(x,y))).1=4)).card:ℝ)-
          udens*(P.neighborFinset x∩vertices).card|<(n:ℝ)^(3/4:ℝ)) ∧
        (∀j∈Tlevel,∀x∈Blevel j,|(((P.neighborFinset x∩Alevel j).filter (fun y=>(z.1 (Sum.inl s(x,y))).1=4)).card:ℝ)-
          udens*(P.neighborFinset x∩Alevel j).card|<((Alevel j).card:ℝ)^(3/4:ℝ)) ∧
        (∀j∈Tlevel,∀w∈Hlevel j,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w (Alevel j)-
          ((Alevel j).card:ℝ)*(1-(∑g,q w g)-(∑k,s w k))|<((Alevel j).card:ℝ)^(3/4:ℝ)) ∧
        (∀j∈Tlevel,∀v∈Alevel j,|rawIntervalUnassignedColumnCount π d (fun e=>z.1 (Sum.inr e)) v (Hlevel j)-
          ∑w∈Hlevel j,(1-(∑g,q w g)-(∑k,s w k))|<((Alevel j).card:ℝ)^(3/4:ℝ)) ∧
        (∀j∈Tlevel,∀v∈Alevel j,
          ((rawIntervalExtendedAnyHubSet π d (fun e=>z.1 (Sum.inr e)) v ∩ Hlevel j).card:ℝ) ≤
            4*((Hlevel j).card:ℝ)/(((r+4):ℕ):ℝ)+4*((Alevel j).card:ℝ)^(3/4:ℝ)) ∧
        (∀j∈Tlevel,∀v∈Alevel j,
          ((rawIntervalBoundaryHubSet π d (fun e=>z.1 (Sum.inr e)) (Hlevel j) v).card:ℝ) ≤
            4*((Hlevel j).card:ℝ)/d+4*((Alevel j).card:ℝ)^(3/4:ℝ)) ∧
        RetainedRestrictionGood π d (fun e=>z.1 (Sum.inr e)) false
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false))
          (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζret z.2 ∧
        (∀u,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) u vertices-
          (vertices.card:ℝ)*(1-(∑g,q u g)-(∑j,s u j))|<(n:ℝ)^(3/4:ℝ)) ∧
        (∀v,|rawIntervalUnassignedColumnCount π d (fun e=>z.1 (Sum.inr e)) v Finset.univ-
          ∑u:U,(1-(∑g,q u g)-(∑j,s u j))|<(n:ℝ)^(3/4:ℝ)) ∧
        (∀x y,x≠y→((5/32:ℝ)*θ^2-1/(4*(d:ℝ)))*Fintype.card U-5*(n:ℝ)^(3/4:ℝ)≤
          (rawProtectedPairHubs π d (fun e=>z.1 (Sum.inr e)) false true
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 x y).card) ∧
        (∀v,((rawIntervalExtendedAnyHubSet π d (fun e=>z.1 (Sum.inr e)) v).card:ℝ)≤
          4*(Fintype.card U:ℝ)/(((r+4):ℕ):ℝ)+4*(n:ℝ)^(3/4:ℝ)) ∧
        (∀x y,x≠y→(5/8:ℝ)*(1/100:ℝ)^2*Fintype.card U-(n:ℝ)^(3/4:ℝ)≤
          (((Finset.univ:Finset U).filter (fun u=>rawIntervalFamilyState π d (fun e=>z.1 (Sum.inr e)) (x,u)=some (Sum.inr false) ∧
            rawIntervalFamilyState π d (fun e=>z.1 (Sum.inr e)) (y,u)=some (Sum.inr false))).card:ℝ)) ∧
        (∀u i,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) u
          (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
          (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*
          (1-(∑g,q u g)-(∑j,s u j))|<(n:ℝ)^(3/4:ℝ)) ∧
        (∀u i,|rawIntervalReservedLabelHubCountOn π d (fun e=>z.1 (Sum.inr e)) u false
          (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
          (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*s u false|<(n:ℝ)^(3/4:ℝ)) ∧
        (∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p₁^2-(n:ℝ)^(3/4:ℝ)-
          2*(2*((3*d:ℕ):ℝ)+1)≤((Finset.univ.filter (fun v=>
            0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) false x v ∧
            0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) false v y)).card:ℝ)) ∧
        (∀u g,|rawIntervalHubStartCount π d g (fun e=>z.1 (Sum.inr e)) u-(n:ℝ)*q u g/d|<(n:ℝ)^(3/4:ℝ)/d) ∧
        MarkedRetainedReservoirSelection r d size a₀ b₀ e₀ f₀ εAbs P π false false ⟨f z.1,z.2⟩ ∧
        MarkedVortexFixedSelection r d size a₀ b₀ e₀ f₀ εAbs P π false false ⟨f z.1,z.2⟩ ∧
        (∀b u,|rawMarkedRestrictedSpokeCol π d (fun e=>z.1 (Sum.inr e)) true true b u Finset.univ-
          (if b then q u true else s u true)*(n:ℝ)|<tHub) ∧
        (∀u,|(((ordinaryCommonHubSpokeRoots u).filter (fun root=>
          longRawHubState P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) true true root=true)).card:ℝ)-
          longAssignedApproxOrdinaryWeight F hF K (r+4) θ u*n|≤tHub) ∧
        rawMarkedSeedConcentrated P π d (r+4) p₂ k₂ q s true true t Wm
          (fun e=>rawExpandedApproximateCollapse e (z.1 e)) ∧
        (∀i,rawOrdinarySeedConcentrated P π d (ni i+2) p₂ k₂ q s true true t (Wo i)
          (fun e=>rawExpandedApproximateCollapse e (z.1 e))) ∧
        (∀i root,longRawHubState P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) true true root=true→
          |resourcePatternLoad (longRawHubResources (U:=U) π d (r+4) (fun i=>ni i+2) i)
            (longMixedSeedWeight Wm Wo i) (fun _ _=>true) root
            (longRawHubState P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) true true)-
            longAssignedMixedTarget F hF K (r+4) θ D p₂ k₂ i root|≤
          t+τ*longAssignedMixedTarget F hF K (r+4) θ D p₂ k₂ i root) ∧
        (∀(Del:SimpleGraph (Fin n)) (δ:ℝ), (∀x,(Del.degree x:ℝ)≤δ)→
          δ≤Δ*n→
          let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
          let hub:=longRawHubNames (U:=U) π d (r+4) ℓ
          let S:=longRawSurvivingResources P π d raw true true Del.edgeFinset
          let e:{v // v∈S}↪_:=Function.Embedding.subtype _
          ∀ztest:LongRetainedHubTest F hF K θ,
            θ*(n:ℝ)/(200*(K:ℝ)*(K:ℝ))≤
              ∑c:RestrictedResource (mixedCandidateResources R) e,
                longRetainedHubIndicator F hF θ hub ztest c.val*mixedCandidateWeight Wmix c.val) ∧
        (∀(Del:SimpleGraph (Fin n)) (δ:ℝ), (∀x,(Del.degree x:ℝ)≤δ)→
          δ≤Δ*n→0≤t+C*(δ/(n:ℝ))+4*τ ∧ t+C*(δ/(n:ℝ))+4*τ≤eps/2) ∧
        (∀(Del:SimpleGraph (Fin n)) (δ:ℝ), (∀x,(Del.degree x:ℝ)≤δ)→
          δ≤Δ*n→
          let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
          let S:=longRawSurvivingResources P π d raw true true Del.edgeFinset
          let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
          let e:S↪LongRawHubResource n U:=Function.Embedding.subtype _
          let Cand:=RestrictedResource (mixedCandidateResources R) e
          let Q:=restrictedResourceSet (mixedCandidateResources R) e
          let fS:=survivingResourceEmbedding S T (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset)
          let φ:=fS.trans (markedRawSampledPhysicalEmbedding P π d raw true true)
          let hub:=longRawHubNames (U:=U) π d (r+4) ℓ
          let test:=fun (j:LongRetainedHubTest F hF K θ) (c:Cand)=>longRetainedHubIndicator F hF θ hub j c.val
          ∃M:Finset Cand,(∀c∈M,0<mixedCandidateWeight Wmix c.val) ∧
            (∀c∈M,∀c'∈M,c≠c'→Disjoint (Q c) (Q c')) ∧
            (∀x,alpha*n≤(rimIncidentResources φ x).card →
              ((rimIncidentResources φ x\M.biUnion Q).card:ℝ)≤γ*(rimIncidentResources φ x).card) ∧
            (∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (alpha*n) (γ*(longRawIncidenceSet S i).card)) ∧
            (∀i,alpha*n≤(longRawIncidenceSet S i).card →
              ((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤γ*(longRawIncidenceSet S i).card) ∧
            (∀j,(1-γ)*(∑c,test j c*mixedCandidateWeight Wmix c.val)≤∑c∈M,test j c) ∧
            (∀j,(∑c∈M,test j c)≤(1+γ)*(∑c,test j c*mixedCandidateWeight Wmix c.val)) ∧
            (∀x,((physicalRimResidualGraph (markedRawSampledPhysicalEmbedding P π d raw true true)
              ((M.map (survivingCandidateEmbedding (mixedCandidateResources R) S T
                (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset))).biUnion
                (restrictedResourceSet (mixedCandidateResources R) (Function.Embedding.subtype (·∈T))))).degree x:ℝ)≤max alpha γ*n+δ) ∧
            let selected:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
            let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false
              (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false
            ∀(Reserve:Finset (Finset (Fin n)⊕(Fin n×U))) (X:Finset (Fin n)) (Z:Finset U),
            MarkedFixedTerminalAbsorber P π d (r+4) selected H Reserve X Z →
            let state:=longRawHubState P π d raw true true
    let T:=bernoulliVertexSet state
    let eraw:{z // z∈T}↪_:=Function.Embedding.subtype _
    let q:=survivingCandidateEmbedding (mixedCandidateResources R) S T (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset)
    let N:=M.map q
    let A:=LongRawSelectedOrdinary π d (r+4) ℓ eraw N
    let Q:=longRawSelectedOrdinaryWheel π d (r+4) ℓ eraw N
    ∃assign:A↪(Σu,(F u).ConnectedComponent),
    ∃C:∀a:A,(F (Q a).val.2).ConnectedComponent,
      (∀a,(⟨(Q a).val.2,C a⟩:Σu,(F u).ConnectedComponent)=assign a) ∧
    (∀u,Fintype.card (longRawSourceDomain F π d (r+4) ℓ eraw N C u) =
      ∑i:Fin K,(N.filter (fun c=>c.val.1=some i ∧
        longRawSeedHub π d (r+4) ℓ c.val.1 c.val.2=u)).card * ℓ i) ∧
    (∀u,Fintype.card {v:Fin n // v∉longRawSourceDomain F π d (r+4) ℓ eraw N C u} =
      n - ∑i:Fin K,(N.filter (fun c=>c.val.1=some i ∧
        longRawSeedHub π d (r+4) ℓ c.val.1 c.val.2=u)).card * ℓ i) ∧
    (∀u,|((Fintype.card (longRawSourceDomain F π d (r+4) ℓ eraw N C u):ℕ):ℝ) -
      (1-θ)*(n:ℝ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i u)| ≤
      ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ))) ∧
    (∀u,|((Fintype.card {v:Fin n // v∉longRawSourceDomain F π d (r+4) ℓ eraw N C u}:ℕ):ℝ) -
      ((n:ℝ)-(1-θ)*(n:ℝ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i u))| ≤
      ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ))) ∧
    (∀u, (n:ℝ)*ordinaryAssignedFraction F hF K u none -
      ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ)) ≤
        ((Fintype.card {v:Fin n // v∉longRawSourceDomain F π d (r+4) ℓ eraw N C u}:ℕ):ℝ) ∧
      ((Fintype.card {v:Fin n // v∉longRawSourceDomain F π d (r+4) ℓ eraw N C u}:ℕ):ℝ) ≤
        (n:ℝ)*(ordinaryAssignedFraction F hF K u none+(101/100:ℝ)*θ) +
          ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ))) ∧
    (∀u v,K<Fintype.card ((F u).connectedComponentMk v)→
      v∉longRawSourceDomain F π d (r+4) ℓ eraw N C u) ∧
    let T:=longRawSourceDomain F π d (r+4) ℓ eraw N C
    ∃ψ:∀u,(T u)↪Fin n,
      (∀u x y,(F u).Adj x.val y.val→
        rawMarkedPairRims P π d raw (Sum.inl (ψ u x,ψ u y)) ∨
        rawMarkedPairRims P π d raw (Sum.inl (ψ u y,ψ u x))) ∧
      (∀u v,u≠v→Disjoint
        (partialFactorPhysicalEdges (T u) ((F u).induce (T u)) (ψ u))
        (partialFactorPhysicalEdges (T v) ((F v).induce (T v)) (ψ v))) ∧
      (∀u x y,(F u).Adj x.val y.val→Sum.inl ({ψ u x,ψ u y}:Finset (Fin n))∉Reserve) ∧
      (∀u x y,(F u).Adj x.val y.val→s(ψ u x,ψ u y)∉Del.edgeFinset)) :=by
  intro ni hni hpadded pstar₀ BMseed₀ BOseed₀ Kpair₀ C₀
  obtain ⟨β,βCommon,εAbs,εRob,ζRob,δAbs,hβ,hβCommon,hεAbs,hεRob,hζRob,hδAbs,hRich⟩:=
    marked_adaptive_agreement_named_probability_assigned k₀ r Qpow hQpow hr hlen αRef ρ₀ sstar ω γRich tstar kstar κ
      hαRef hρ₀ hsstar hω hmargin hγRich hγRich1 htstar htstar1 horder hkstar hκ
  refine ⟨β,βCommon,εAbs,εRob,ζRob,δAbs,hβ,hβCommon,hεAbs,hεRob,hζRob,hδAbs,?_⟩
  intro εRef δRef ηRich χ χCommon Csize Qreal pstarRef ζ εBal Kbal ζBal χBal εNbr Knbr ζNbr χNbr Bload εLoad Kload ζLoad χLoad ζLocal χLocal ζConfig χConfig
    hεRef hδRef hηRich hηRich1 hχ hχCommon hpstarRef hζ hεBal hKbal hζBal hχBal hεNbr hKnbr hζNbr hχNbr hBload hεLoad hKload hζLoad hχLoad hζLocal hχLocal hζConfig hχConfig hQreal hNbr hpstarBound hgap
  intro Cscale δrow δhub δcol δocc δbd hCscale hδrow hδbound hδhub hδcol hδocc hδbd hδhubgap
  let εrich:ℝ:=ε₀-δhub-δcol-δocc-δbd
  have hRichGap:χ+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig<εrich:=by
    dsimp [εrich]
    linarith only [hgap,hδhubgap]
  obtain ⟨MLevel,hMLevel,hRich⟩:=hRich εRef δRef ηRich χ χCommon Csize Qreal pstarRef ζ εBal Kbal ζBal χBal εNbr Knbr ζNbr χNbr Bload εLoad Kload ζLoad χLoad ζLocal χLocal ζConfig χConfig
    hεRef hδRef hηRich hηRich1 hχ hχCommon hpstarRef hζ hεBal hKbal hζBal hχBal hεNbr hKnbr hζNbr hχNbr hBload hεLoad hKload hζLoad hχLoad hζLocal hχLocal hζConfig hχConfig εrich hQreal hRichGap hNbr d hd
  obtain ⟨η,hη,t₀,τ₀,Δ,ξ,ht₀,hτ₀,hτhalf,hΔ,hξ,hξeps,N,hMatch⟩:=
    long_assigned_reference_matching_with_inner_domains_and_local_rim_family K (r+4) d hK3 hm hd θ ρ₀ BM hθpos hθ hρ₀ hBM hspace BO hBO ζret hζret alpha γ ε₀ eps lam hε₀ heps heps1 hγε hlam hlamθ hepsAssign halpha halphaMass hγ Cscale δrow hCscale hδrow hδbound
  refine ⟨MLevel,hMLevel,η,hη,t₀,τ₀,Δ,ξ,ht₀,hτ₀,hτhalf,hΔ,hξ,hξeps,N,?_⟩
  intro size
  obtain ⟨a₀,b₀,e₀,aRob,bRob,eRob,hRich⟩:=hRich size
  refine ⟨a₀,b₀,e₀,aRob,bRob,eRob,?_⟩
  intro f₀
  obtain ⟨NHost,hNHost,hRich⟩:=hRich f₀
  refine ⟨NHost,?_⟩
  intro n hn U _ _ F hF Allowed hAllowed ρ D hρlo hρ1 hD hsize hcut hclass P π τ A weight hw hDlo hDhi w hw0 hwupper huv hnoshort vertices Ilevel Tlevel Alevel Blevel Hlevel hminCol hminOcc hminBd hJpos hJA hminHub hHlevel hmin hinjLevel hBlevel εHost he hdeg hbudgetV hbudgetE hτnonneg hτbound
  have hUpos:0<Fintype.card U:=by
    have hρpos:0<ρ:=lt_of_lt_of_le hρ₀ hρlo
    have hp:0<(Fintype.card U:ℝ):=by nlinarith
    exact_mod_cast hp
  have hUnonempty:(Finset.univ:Finset U).Nonempty:=by
    letI:Nonempty U:=Fintype.card_pos_iff.mp hUpos
    exact Finset.univ_nonempty
  intro W Z Hdom _ _ _ _ _ _ hεHostAbs hmind fV gV ρi hcomm L hLsize hnlevels hnZ hstep hZlo hZhi hZW hHW
    Aset Bset Scale hA hB hScale hAS hBS hInv hWS hZS hstepA hstepB hWA hZA hWB hPdomain
    Dbal δPbal hδbal hδbalε hPbal Dlevel δP hδP hδPε hPreg hPmin
    bdom Dload τLevel Aload levelWeight hDloadlo hDloadhi hwLevel hpstar0 hkstar0 htstar0
  intro t tHub b a p₁ k₁ p₂ k₂ udens q s hLaw μ f pstar BMseed BOseed Wm Wo C ℓ Wmix R Pair Kpair failure Ret ν Prior
  have hnpos:0<n:=by omega
  have hnMatch:max N 1≤n:=by omega
  have hnRich:NHost≤n:=by omega
  letI : Nonempty (Fin n):=⟨⟨0,hnpos⟩⟩
  have hUlo:=marked_adaptive_host_index_lower n (Fintype.card U) ρ₀ ρ D ω hρ₀.le hρlo hDlo hsize hωBound
  have hnear:∀v,|(P.degree v:ℝ)-D|≤δAbs*n:=fun v=>(hdeg v).trans
    (mul_le_mul_of_nonneg_right hεHostAbs (Nat.cast_nonneg n))
  have hmass:=marked_adaptive_reference_mass_from_host n (Fintype.card U) ρ₀ ρ D (1/100) (((r+4):ℕ):ℝ) pstarRef
    hρ₀.le hρlo hDlo hsize (by norm_num) (by positivity) hpstarBound
  have hρ:0<ρ:=hρ₀.trans_le hρlo
  have hDp:∀i≤L,(ρ*(1/100)/2)*Dbal i=(1/100)*(Bset i).card:=by
    intro i hi
    exact marked_adaptive_canonical_centre ρ (1/100) ((Bset i).card:ℝ) hρ
  have hLoadEq:∀i≤L,(Fintype.card (Hdom i):ℝ)*(1/100)=Dload i*(ρ*(1/100)/2):=by
    intro i hi
    exact marked_adaptive_canonical_load ρ (1/100) (Fintype.card (Hdom i):ℝ) hρ
  have hLevels:=fun i hi=>marked_adaptive_level_balances ρ (1/100) (((r+4):ℕ):ℝ) (Dbal i) (Dload i)
    ((Bset i).card:ℝ) (Fintype.card (Hdom i):ℝ) (by positivity) (hDp i hi) (hLoadEq i hi)
  have hDk:=fun i hi=>(hLevels i hi).1
  have hLk:=fun i hi=>(hLevels i hi).2.1
  have hLp:=fun i hi=>(hLevels i hi).2.2
  have hh:=hRich (Fin n) U Bool Bool W Z Hdom (by simpa using hnRich) (by simpa using hUlo) (by simpa using huv) P π hnoshort
    D (by simpa using hDlo) (by simpa using hDhi) (by simpa using hnear) (by simpa using hmind) fV gV ρi hcomm L (by simpa using hLsize)
    hnlevels hnZ hstep hZlo hZhi hZW hHW Aset Bset Scale hA hB hScale hAS hBS hInv hWS hZS hstepA hstepB hWA hZA hWB hPdomain
    Dbal δPbal hδbal hδbalε hPbal Dlevel δP hδP hδPε hPreg hPmin
    bdom Dload τLevel Aload levelWeight hDloadlo hDloadhi hwLevel ρ (1/100) hρlo hρ1 hsstar1 (by norm_num)
    hpstar0 hkstar0 htstar0 (by simpa using hmass) hDp hDk hLk hLp q hLaw.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.1 s hLaw.2.2.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.2.2 false false
    (by intro u;rfl) (by intro u;rfl)
  have hpriorRich:1-εrich≤(rawMarkedRetentionLaw π d hd false p₁ k₁ hLaw.1 hLaw.2.1 (by dsimp only [p₁,k₁]; have hp:=hLaw.2.2.1; have hk:=hLaw.2.2.2.1; have hu:=hLaw.2.2.2.2.1; have hh:=hLaw.2.2.2.2.2.1; linarith)
      q hLaw.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.1 s hLaw.2.2.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.2.2).probability Prior:=by
    convert hh using 1 <;> congr 4 <;> first | rfl | exact Subsingleton.elim _ _
  let Base:=rawMarkedRetentionLaw π d hd false p₁ k₁ hLaw.1 hLaw.2.1 (by dsimp only [p₁,k₁]; have hp:=hLaw.2.2.1; have hk:=hLaw.2.2.2.1; have hu:=hLaw.2.2.2.2.1; have hh:=hLaw.2.2.2.2.2.1; linarith)
    q hLaw.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.1 s hLaw.2.2.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.2.2
  let HubGood:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d false→Prop:=fun z=>
    ∀j∈Tlevel,∀w∈Hlevel j,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w (Alevel j)-
      ((Alevel j).card:ℝ)*(1-(∑g,q w g)-(∑k,s w k))|<((Alevel j).card:ℝ)^(3/4:ℝ)
  have hHub:1-δhub≤Base.probability HubGood:=by
    have hspec:=(Classical.choose_spec (raw_retained_unassigned_hub_local_family_small_failure d hd (1/2) δhub (by norm_num) hδhub)).2
    have hh:=hspec (Fin n) U Bool Bool Ilevel Tlevel Alevel Hlevel (by simpa [retainedUnassignedHubThreshold] using hminHub) hinjLevel hHlevel
      π false p₁ k₁ hLaw.1 hLaw.2.1 (by dsimp only [p₁,k₁]; have hp:=hLaw.2.2.1; have hk:=hLaw.2.2.2.1; have hu:=hLaw.2.2.2.2.1; have hh:=hLaw.2.2.2.2.2.1; linarith)
      q hLaw.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.1 s hLaw.2.2.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.2.2 hnoshort
    simpa only [Base,HubGood] using hh
  let ColGood:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d false→Prop:=fun z=>
    ∀j∈Tlevel,∀v∈Alevel j,|rawIntervalUnassignedColumnCount π d (fun e=>z.1 (Sum.inr e)) v (Hlevel j)-
      ∑w∈Hlevel j,(1-(∑g,q w g)-(∑k,s w k))|<((Alevel j).card:ℝ)^(3/4:ℝ)
  have hCol:1-δcol≤Base.probability ColGood:=by
    have hspec:=(Classical.choose_spec (raw_retained_unassigned_column_local_family_small_failure d hd δcol hδcol)).2
    have hh:=hspec (Fin n) U Bool Bool Ilevel Tlevel Alevel Hlevel (by simpa [retainedUnassignedColumnThreshold] using hminCol) hinjLevel hJpos hJA
      π false p₁ k₁ hLaw.1 hLaw.2.1 (by dsimp only [p₁,k₁]; have hp:=hLaw.2.2.1; have hk:=hLaw.2.2.2.1; have hu:=hLaw.2.2.2.2.1; have hh:=hLaw.2.2.2.2.2.1; linarith)
      q hLaw.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.1 s hLaw.2.2.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.2.2 hnoshort
    simpa only [Base,ColGood] using hh
  let OccGood:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d false→Prop:=fun z=>
    ∀j∈Tlevel,∀v∈Alevel j,
      ((rawIntervalExtendedAnyHubSet π d (fun e=>z.1 (Sum.inr e)) v ∩ Hlevel j).card:ℝ) ≤
        4*((Hlevel j).card:ℝ)/(((r+4):ℕ):ℝ)+4*((Alevel j).card:ℝ)^(3/4:ℝ)
  have hOcc:1-δocc≤Base.probability OccGood:=by
    have hqM:∀u g,q u g≤1/(((r+4):ℕ):ℝ):=by
      intro u g
      exact long_assigned_interval_probability_upper (by omega) F hF K (r+4) (by omega) θ hθpos.le u g
    have hspec:=(Classical.choose_spec (raw_retained_absorber_occurrence_local_small_failure d hd δocc hδocc)).2
    have hh:=hspec (Fin n) U Bool Ilevel Tlevel Alevel Hlevel (by simpa [retainedAbsorberOccurrenceThreshold] using hminOcc) hinjLevel hJpos hJA
      π false p₁ k₁ hLaw.1 hLaw.2.1 (by dsimp only [p₁,k₁]; have hp:=hLaw.2.2.1; have hk:=hLaw.2.2.2.1; have hu:=hLaw.2.2.2.2.1; have hh:=hLaw.2.2.2.2.2.1; linarith)
      q hLaw.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.1 s hLaw.2.2.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.2.2 hnoshort (((r+4):ℕ):ℝ) (by positivity) hqM
    simpa only [Base,OccGood] using hh
  let BoundaryGood:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d false→Prop:=fun z=>
    ∀j∈Tlevel,∀v∈Alevel j,
      ((rawIntervalBoundaryHubSet π d (fun e=>z.1 (Sum.inr e)) (Hlevel j) v).card:ℝ) ≤
        4*((Hlevel j).card:ℝ)/d+4*((Alevel j).card:ℝ)^(3/4:ℝ)
  have hBoundary:1-δbd≤Base.probability BoundaryGood:=by
    have hspec:=(Classical.choose_spec (raw_retained_boundary_hubs_local_small_failure d hd δbd hδbd)).2
    have hh:=hspec (Fin n) U Bool Ilevel Tlevel Alevel Hlevel (by simpa [retainedBoundaryHubsThreshold] using hminBd) hinjLevel hJpos hJA
      π false p₁ k₁ hLaw.1 hLaw.2.1 (by dsimp only [p₁,k₁]; have hp:=hLaw.2.2.1; have hk:=hLaw.2.2.2.1; have hu:=hLaw.2.2.2.2.1; have hh:=hLaw.2.2.2.2.2.1; linarith)
      q hLaw.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.1 s hLaw.2.2.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.2.2 hnoshort
    simpa only [Base,BoundaryGood] using hh
  let Prior':RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d false→Prop:=fun z=>Prior z ∧ (((HubGood z ∧ ColGood z) ∧ OccGood z) ∧ BoundaryGood z)
  have hprior:1-ε₀≤Base.probability Prior':=by
    have hBoth:=finiteLaw_intersection_lower Base HubGood ColGood δhub δcol hHub hCol
    have hAll:=finiteLaw_intersection_lower Base (fun z=>HubGood z ∧ ColGood z) OccGood (δhub+δcol) δocc (by linarith only [hBoth]) hOcc
    have hAllBoundary:=finiteLaw_intersection_lower Base (fun z=>(HubGood z ∧ ColGood z) ∧ OccGood z) BoundaryGood (δhub+δcol+δocc) δbd (by linarith only [hAll]) hBoundary
    have hh:=finiteLaw_intersection_lower Base Prior (fun z=>((HubGood z ∧ ColGood z) ∧ OccGood z) ∧ BoundaryGood z) εrich (δhub+δcol+δocc+δbd) hpriorRich (by linarith only [hAllBoundary])
    dsimp only [Prior',εrich] at hh
    linarith only [hh]
  obtain ⟨z,hz,hEvent,hRim,hFamily,hRows,hInner,hColumn,hPairs,hOccupancy,hReservedPairs,hNeighbour,hReservedNeighbour,hPath,hStarts,hRest⟩:=hMatch n hnMatch U F hF Allowed hAllowed ρ D hρlo hρ1 hD hsize hcut hclass P π τ A weight hw hDlo hDhi w hw0 hwupper huv hnoshort vertices Ilevel Tlevel Alevel Blevel hmin hinjLevel hBlevel Finset.univ hUnonempty εHost he hdeg hbudgetV hbudgetE hτnonneg hτbound Prior' hprior
  refine ⟨z,hz,hEvent.1,hRim,hFamily,?_,?_,?_,?_,hRows,hInner,hColumn,hPairs,hOccupancy,hReservedPairs,hNeighbour,hReservedNeighbour,hPath,hStarts,?_,?_,hRest⟩
  · simpa only [HubGood,f,rawExpandedMarkedCollapse,id_eq] using hEvent.2.1.1.1
  · simpa only [ColGood,f,rawExpandedMarkedCollapse,id_eq] using hEvent.2.1.1.2
  · simpa only [OccGood,f,rawExpandedMarkedCollapse,id_eq] using hEvent.2.1.2
  · simpa only [BoundaryGood,f,rawExpandedMarkedCollapse,id_eq] using hEvent.2.2
  · exact marked_adaptive_agreement_reservoir_selection r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
      β βCommon εAbs εRob ζRob εRef δRef γRich p₁ k₁ (1/100) tstar ζ εBal ζBal εNbr ζNbr Bload εLoad Kload ζLoad ζLocal ζConfig ρ₀ sstar kstar τLevel
      P π fV gV ρi Aset Bset Scale Dlevel Dload bdom levelWeight q s false false ⟨f z.1,z.2⟩ hEvent.1
  · exact marked_adaptive_agreement_vortex_fixed_selection r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
      β βCommon εAbs εRob ζRob εRef δRef γRich p₁ k₁ (1/100) tstar ζ εBal ζBal εNbr ζNbr Bload εLoad Kload ζLoad ζLocal ζConfig ρ₀ sstar kstar τLevel
      P π fV gV ρi Aset Bset Scale Dlevel Dload bdom levelWeight q s false false ⟨f z.1,z.2⟩ hEvent.1
end Oberwolfach
