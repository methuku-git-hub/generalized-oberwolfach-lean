module

public import Oberwolfach.MarkedJointReferenceUniformFailure
public import Oberwolfach.MixedClassMarkedPreparationUniformInvCard
public import Oberwolfach.MarkedInitialIndexCardBounds

@[expose] public section
/-! Combine the actual fixed-vortex reference event with the seven expanded
preparation events under the manuscript's conditional retention law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_reference_expanded_preparation_and_extra_uniform
    (r h k₀:ℕ) (hr:2≤r) (hlen:r+4+1=(k₀+2)*2)
    (α ρ₀ sstar tstar kstar:ℝ)
    (hα:0<α) (hα1:α≤1) (hρ₀:0<ρ₀) (hsstar:0<sstar) (htstar:0<tstar) (htstar1:tstar≤1)
    (horder:tstar≤sstar) (hkstar:0<kstar)
    (hmargin:successorCycleRatio k₀+α/4≤1/2+α/2)
    :
    ∃ εAbs ζAbs δAbs:ℝ,0<εAbs ∧ 0<ζAbs ∧ 0<δAbs ∧
    ∃ βconfig βCommon:ℝ,0<βconfig ∧ 0<βCommon ∧
    ∀ tolRef pstarRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr:ℝ,
    0<tolRef→0<pstarRef→pstarRef≤ρ₀*tstar/4→0<ζActive→
    0<τ→0<tolLocal→0<ζLocal→0<τParent→0<tolParent→0<ζParent→0<epsBal→0<ζBal→0<ζCut→0<ζCfg→0<rowErr→
    ∃ βmax:ℝ,0<βmax ∧ ∀ χ:ℝ,0<χ→∀ ζCommon:ℝ,0<ζCommon→
    ∀ εref δref β ε:ℝ,
    0<εref→0<δref→0≤β→β≤βmax→β≤εref/4→0<ε→ε<1/4→
    ∀ ζWide ζRow:ℝ,0<ζWide→0<ζRow→∀ (d:ℕ) (hd:2≤d),∃ m₀:ℕ,1≤m₀ ∧
    ∀ size:ℕ,∃ a₀ b₀ e₀:ℕ,∀ f₀:ℕ,∃ n₀:ℕ,
    ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ),G.IsRegularOfDegree D→∀ (hn:0<Fintype.card V),
    (1/2+α)*Fintype.card V≤(D:ℝ)→∀ (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1),
    m₀≤m→n₀≤Fintype.card V→m≤Fintype.card V→∀ (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
      (hpres:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
    (∀ x l,0<l→l<2*d+1→(π^l) x≠x)→∀ L:ℕ,L<Q.length→
    letI : Nonempty V:=Fintype.card_pos_iff.mp hn
    let W:=fun i=>markedVortexVertexType Q i
    let Z:=fun i=>markedVortexHubType Q i
    let A:∀ i,Finset (W i):=fun i=>Finset.univ\markedVortexInnerVertices Q i
    let B:∀ i,Finset (Z i):=fun i=>Finset.univ\markedVortexInnerHubs Q i
    let X:=fun i=>↥(A i)
    let f:=fun i=>markedVortexActiveVertexEmbedding Q i
    let g:=fun i=>markedVortexActiveHubEmbedding Q i
    let ρ:=fun i=>markedVortexActivePermutation Q π hpres i
    let Dactive:=fun i=>2*((B i).card:ℝ)/initialIndexDensity U D
    let pstarLocal:=ρ₀*sstar/(2*((r+4:ℕ):ℝ))
    let fParent:=markedVortexVertexEmbedding Q
    let gParent:=markedVortexHubEmbedding Q
    let gWide:=markedVortexNonDeeperHubToPhysical Q
    let ρParent:=markedVortexPermutation Q π hpres
    let Dparent:=fun i=>2*(Fintype.card (Z i):ℝ)/initialIndexDensity U D;
    ∃ weightParent:∀ i,(Fin (r+4+1)→W i)→ℝ,
    ∃ weight:∀ i,(Fin (r+4+1)→X i)→ℝ,
    (∀ i≤L,SuccessorSequenceWeightConditions (G.comap (fParent i)) (ρParent i) (3*d)
      (Dparent i) τParent (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weightParent i)) ∧
    (∀ i≤L+1,SuccessorSequenceWeightConditions (G.comap (f i)) (ρ i) (3*d)
      (Dactive i) τ (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weight i)) ∧
    ∀ (s₀:ℝ) (hslo:sstar≤s₀) (hshi:s₀≤1/100),
    let dens:=initialIndexDensity U D
    let densities:=marked_seed_density_bounds (r+4) (by omega) dens s₀ ρ₀ sstar hρ₀ hsstar hρlo hρhi hslo hshi
    let p:=dens*s₀/2
    let kval:=p/((r+4:ℕ):ℝ);
    kstar≤p→kstar≤kval→
    ∀ (q:U→Bool→ℝ) (hq:∀ u a,0≤q u a) (hQ:∀ u,∑ a,q u a≤1/8)
      (s:U→Bool→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a)) (a:Bool) (j:Bool),
      (∀ u,q u a=s₀/((r+4:ℕ):ℝ))→(∀ u,s u j=s₀)→tstar≤s₀/((r+4:ℕ):ℝ)→
    let Eref:=MarkedReferenceActiveAbsorberProperty r h d (α/2) βconfig εref δref tolRef ζActive ζAbs tstar εAbs
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j
    let EParent:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d a=>
      (∀ i≤L,∀ δ:ℝ,0≤δ→∀ (DR:SimpleGraph (W i)) (DS:SimpleGraph (W i⊕Z i)),
        (∀ x,(DR.degree x:ℝ)≤δ)→(∀ x,(DS.degree x:ℝ)≤δ)→
        MarkedPackingLoadsWithSpokes (G.comap (fParent i)) (ρParent i) d (r+4) (Dparent i) p kval s₀ (weightParent i) a j
          (Function.Embedding.refl (Z i)) (fun u=>q (gParent i u)) (fun u=>s (gParent i u))
          (τParent+tolParent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/pstarLocal^(2*(r+4)+1))*ζParent+
            33*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/pstarLocal^(2*(r+4)+1))*δ/Fintype.card (W i))
          (rawMarkedDeleteRims (rawMarkedRestrictPair (fParent i) (gParent i) z.1) DR.edgeFinset)
          (markedDeletePhysicalSpokes
            (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
              (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (fParent i x) (gParent i u)) DS)) ∧
        (∀ i≤L+1,MarkedLocalSpokeLoadsWithSpokes (G.comap (f i)) (ρ i) d (r+4) (Dactive i) p kval s₀ (weight i)
        (τ+tolLocal+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/pstarLocal^(2*(r+4)+1))*ζLocal)
        (rawMarkedRestrictPair (f i) (g i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u))) ∧ Eref z;
    let fCut:=fun i=>markedVortexVertexEmbedding Q (i+1)
    let gCut:=fun i=>markedVortexHubEmbedding Q (i+1)
    let ρCut:=fun i=>markedVortexPermutation Q π hpres (i+1)
    let ECut:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d a=>∀ i≤L,
      MarkedCutFamiliesWithSpokes (G.comap (fCut i)) (ρCut i) d (α/2) p kval tstar ζCut
        (rawMarkedRestrictPair (fCut i) (gCut i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (fCut i x) (gCut i u));
    let EConfig:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d a=>∀ i≤L,
      MarkedLocalConfigurationsWithSpokes r (G.comap (fParent i)) (ρParent i) d Finset.univ
        (markedLocalCycleCoefficient r (α/2) (tstar/2) kstar-(r+5:ℕ)*ζCfg)
        (markedLocalPathCoefficient r (α/2) (tstar/2) kstar-(r+4:ℕ)*ζCfg)
        (rawMarkedRestrictPair (fParent i) (gParent i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (fParent i x) (gParent i u));
    let EActive:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d a=>∀ i≤L,
      MarkedLocalConfigurationsWithSpokes r (G.comap (f (i+1))) (ρ (i+1)) d Finset.univ
        (markedLocalCycleCoefficient r (α/2) (tstar/2) kstar-(r+5:ℕ)*ζCfg)
        (markedLocalPathCoefficient r (α/2) (tstar/2) kstar-(r+4:ℕ)*ζCfg)
        (rawMarkedRestrictPair (f (i+1)) (gParent i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f (i+1) x) (gParent i u));
    let EWide:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d a=>∀ i≤L,
      MarkedLocalSpokeLoadsWithSpokes (G.comap (f (i+1))) (ρ (i+1)) d (r+4) (Dactive (i+1)) p kval s₀ (weight (i+1))
        (τ+tolLocal+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/pstarLocal^(2*(r+4)+1))*(4/ε)*ζWide)
        (rawMarkedRestrictPair (f (i+1)) (gWide i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f (i+1) x) (gWide i u));
    let ERow:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d a=>∀ i≤L,
      MarkedRowsWithSpokes (G.comap (f (i+1))) (ρ (i+1)) d 1 Finset.univ p kval
        (fun u=>q (gWide i u)) (fun u=>s (gWide i u)) a j ((rowErr+ζRow)*Fintype.card (X (i+1)))
        (rawMarkedRestrictPair (f (i+1)) (gWide i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f (i+1) x) (gWide i u));
    let ECommon:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d a=>∀ i≤L,
      MarkedCommonConfigurationsWithSpokes r (G.comap (fParent i)) (ρParent i) d βCommon ζCommon
        (rawMarkedRestrictPair (fParent i) (gParent i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (fParent i x) (gParent i u));
    let EFull:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d a=>∀ i≤L,
      MarkedRowsWithSpokes (G.comap (fParent i)) (ρParent i) d (r+12) Finset.univ p kval
        (fun u=>q (gParent i u)) (fun u=>s (gParent i u)) a j
        ((tolRef+(r+12:ℕ)*ζActive)*Fintype.card (W i))
        (rawMarkedRestrictPair (fParent i) (gParent i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (fParent i x) (gParent i u)) ∧
      MarkedIndicesWithSpokes (ρParent i) d (r+12) Finset.univ
        (fun u=>q (gParent i u)) (fun u=>s (gParent i u)) a j
        ((tolRef+(r+12:ℕ)*ζActive)*Fintype.card (Z i))
        (rawMarkedRestrictPair (fParent i) (gParent i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (fParent i x) (gParent i u));
    let EAgreement:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d a=>∀ i≤L,
      let ω:=rawMarkedRestrictPair (fParent i) (gParent i) z.1
      let H:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (fParent i x) (gParent i u);
      (∀ b x,(∑ u,if ¬(rawMarkedPairSpokes (ρParent i) d ω a j b x u↔H b x u) then (1:ℝ) else 0)≤ζActive*Fintype.card (Z i)) ∧
      (∀ b u,(∑ x,if ¬(rawMarkedPairSpokes (ρParent i) d ω a j b x u↔H b x u) then (1:ℝ) else 0)≤ζActive*Fintype.card (W i));
    let EActualCuts:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d a=>∀ i≤L,
      MarkedReferenceCutFamilies (G.comap (fParent i)) (ρParent i) d a j (α/8) p kval
        (s₀/((r+4:ℕ):ℝ)) (rawMarkedRestrictPair (fParent i) (gParent i) z.1);
    ∀ (Z T:SimpleGraph V),T≤G→∀ (I:Finset V) (J:Finset U),J.Nonempty→
    ∀ (p₂ k₂ u:ℝ) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u) (hsum:2*p+2*kval+2*p₂+2*k₂+u≤1),
    let Ref:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d a=>MarkedActualVortexBalanceProperty Q π hpres d (r+4) L a j epsBal ζBal
        (markedVortexInnerVertices Q) (markedVortexInnerHubs Q) z ∧
      (L=0 ∨ MarkedActualVortexBalanceProperty Q π hpres d (r+4) (L-1) a j epsBal ζBal
        (markedVortexDeeperVertices Q) (markedVortexDeeperHubs Q) z) ∧ EActualCuts z ∧ EAgreement z ∧ EFull z ∧ ERow z ∧ EWide z ∧ EActive z ∧ ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z
    let ρexpanded:=markedExpandedPhysicalProbability p kval p₂ k₂ u
    let μexpanded:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p kval p₂ k₂ u
      (densities.1.trans_le densities.2.1).le (densities.1.trans_le densities.2.2.1).le hp₂ hk₂ hu hsum
      d hd q hq hQ s hs hS)
    let fexpanded:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e) e=>rawExpandedMarkedCollapse e (ω e);
    let Base:(Σ ω:(∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e),
      mixedClassRetentionSpace true π d a ω)→Prop := fun z=>
      expandedPhysicalDegreeGood G Z ρexpanded (fun e=>z.1 (Sum.inl e)) ∧
      (∀ x y,x≠y→|(eligibleTwoPathCount T (sampledColourOrientation G (fun e=>markedExpandedClass (z.1 (Sum.inl e))) 0) x y:ℝ)-
        ((T.neighborFinset x∩T.neighborFinset y).card:ℝ)*((2*p+2*kval+2*p₂+2*k₂+u)/2)^2|<(Fintype.card V:ℝ)^(3/5:ℝ)) ∧
      (∀ g a,|((rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g a).card:ℝ)-(∑ u,q u g/(d:ℝ))|<(Fintype.card V:ℝ)^(3/5:ℝ)) ∧
      (∀ u g,|rawIntervalHubStartCount π d g (fun e=>z.1 (Sum.inr e)) u-(Fintype.card V:ℝ)*q u g/d|<
        (Fintype.card V:ℝ)^(3/4:ℝ)/d) ∧
      ((∀ w,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w I-(I.card:ℝ)*(1-(∑ g,q w g)-(∑ j,s w j))|<(Fintype.card V:ℝ)^(3/4:ℝ)) ∧
       (∀ v,|rawIntervalUnassignedColumnCount π d (fun e=>z.1 (Sum.inr e)) v J-∑ w∈J,(1-(∑ g,q w g)-(∑ j,s w j))|<(Fintype.card V:ℝ)^(3/4:ℝ))) ∧
      ((∀ w,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w Finset.univ-(Fintype.card V:ℝ)*(1-(∑ g,q w g)-(∑ j,s w j))|<(Fintype.card V:ℝ)^(3/4:ℝ)) ∧
       (∀ v,|rawIntervalUnassignedColumnCount π d (fun e=>z.1 (Sum.inr e)) v Finset.univ-∑ w,(1-(∑ g,q w g)-(∑ j,s w j))|<(Fintype.card V:ℝ)^(3/4:ℝ))) ∧
      (∀ x,|(((G.neighborFinset x∩I).filter (fun y=>(z.1 (Sum.inl s(x,y))).1=4)).card:ℝ)-u*(G.neighborFinset x∩I).card|<(Fintype.card V:ℝ)^(3/4:ℝ)) ∧ Ref ⟨fexpanded z.1,z.2⟩;
    ∀ (Extra:(Σ ω:(∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e),
      mixedClassRetentionSpace true π d a ω)→Prop) (extraErr:ℝ),
    1-extraErr≤(μexpanded.sigma (mixedClassActualRetention true π d a)).probability Extra→
    1-100*χ-107/(Fintype.card V:ℝ)-extraErr≤(μexpanded.sigma (mixedClassActualRetention true π d a)).probability
      (fun z=>Base z ∧ Extra z) :=by
  obtain ⟨εAbs,ζAbs,δAbs,hεAbs,hζAbs,hδAbs,βconfig,βCommon,hβconfig,hβCommon,hRef⟩:=
    marked_joint_reference_all_levels_uniform_failure r h k₀ hr hlen α ρ₀ sstar tstar kstar hα hα1 hρ₀ hsstar htstar htstar1 horder hkstar hmargin
  refine ⟨εAbs,ζAbs,δAbs,hεAbs,hζAbs,hδAbs,βconfig,βCommon,hβconfig,hβCommon,?_⟩
  intro tolRef pstarRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr
    htolRef hpstarRef hpstarRefBound hζActive hτ htolLocal hζLocal hτParent htolParent hζParent hepsBal hζBal hζCut hζCfg hrowErr
  obtain ⟨βmax,hβmax,hRef⟩:=hRef tolRef pstarRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr
    htolRef hpstarRef hpstarRefBound hζActive hτ htolLocal hζLocal hτParent htolParent hζParent hepsBal hζBal hζCut hζCfg hrowErr
  refine ⟨βmax,hβmax,?_⟩
  intro χ hχ ζCommon hζCommon εref δref β ε hεref hδref hb hbmax hbε he he1 ζWide ζRow hζWide hζRow d hd
  obtain ⟨m₀,hm₀,hRef⟩:=hRef χ hχ ζCommon hζCommon εref δref β ε hεref hδref hb hbmax hbε he he1 ζWide ζRow hζWide hζRow d hd
  obtain ⟨Nbasic,hBasic⟩:=mixed_class_marked_preparation_uniform_invCard d hd
  refine ⟨m₀,hm₀,?_⟩
  intro size
  obtain ⟨a₀,b₀,e₀,hRef⟩:=hRef size
  refine ⟨a₀,b₀,e₀,?_⟩
  intro f₀
  obtain ⟨Nref,hRef⟩:=hRef f₀
  refine ⟨max Nref Nbasic,?_⟩
  intro V U _ _ _ _ G D m hreg hn hD hρlo hρhi hm hnBound hmn Q π hpres hshort L hL
    W Z0 A B X f g ρ Dactive pstarLocal fParent gParent gWide ρParent Dparent
  letI : Nonempty V:=Fintype.card_pos_iff.mp hn
  obtain ⟨weightParent,weight,hwParent,hw,hRef⟩:=hRef V U G D m hreg hn hD hρlo hρhi hm (by omega) hmn Q π hpres hshort L hL
  refine ⟨weightParent,weight,hwParent,hw,?_⟩
  intro s₀ hslo hshi dens densities p kval hpmin hkmin q hq hQ s hs hS a j hq0 hs0 htlo
    Eref EParent fCut gCut ρCut ECut EConfig EActive EWide ERow ECommon EFull EAgreement EActualCuts
    Z T hTG I J hJ p₂ k₂ u hp₂ hk₂ hu hsum Ref ρexpanded μexpanded fexpanded Base Extra extraErr hExtra
  have hU:=marked_initial_index_card_bounds G D hreg hn α ρ₀ hα hρ₀ hD hρlo hρhi
  have hRefTrue:=hRef Bool Bool s₀ hslo hshi hpmin hkmin q hq hQ s hs hS a j hq0 hs0 htlo (fun _=>True) 0 (by simp [finiteLaw_probability_true])
  have hnR:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hpow:(Fintype.card V:ℝ)^(-(1:ℝ))=1/(Fintype.card V:ℝ):=by rw [Real.rpow_neg hnR.le,Real.rpow_one];ring
  have hprob:1-(100*χ+100/(Fintype.card V:ℝ))≤(rawMarkedRetentionLaw π d hd a p kval
      (densities.1.trans_le densities.2.1).le (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).probability Ref:=by
    rw [hpow] at hRefTrue
    simp only [sub_zero, and_true] at hRefTrue
    have h100:(100:ℝ)/(Fintype.card V:ℝ)=100*(1/(Fintype.card V:ℝ)):=by ring
    change 1-100*χ-100*(1/(Fintype.card V:ℝ))≤(rawMarkedRetentionLaw π d hd a p kval
      (densities.1.trans_le densities.2.1).le (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).probability Ref at hRefTrue
    linarith [hRefTrue,h100]
  have hh:=hBasic (100*χ+100/(Fintype.card V:ℝ)) V (by omega) U hU.1 hU.2 G Z T hTG π I J hJ p kval p₂ k₂ u
    (densities.1.trans_le densities.2.1).le (densities.1.trans_le densities.2.2.1).le hp₂ hk₂ hu hsum hshort q hq hQ s hs hS a Ref hprob
  have h107:(107:ℝ)/(Fintype.card V:ℝ)=7/(Fintype.card V:ℝ)+100/(Fintype.card V:ℝ):=by ring
  have hbase:1-100*χ-107/(Fintype.card V:ℝ)≤
      (μexpanded.sigma (mixedClassActualRetention true π d a)).probability Base:=by
    rw [h107]
    have heq:1-100*χ-(7/(Fintype.card V:ℝ)+100/(Fintype.card V:ℝ))=
        1-7/(Fintype.card V:ℝ)-(100*χ+100/(Fintype.card V:ℝ)):=by ring
    rw [heq]
    exact hh
  have hjoin:=finiteLaw_good_intersection (μexpanded.sigma (mixedClassActualRetention true π d a)) Base Extra extraErr hExtra
  linarith
end Oberwolfach
