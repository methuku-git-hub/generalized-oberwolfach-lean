module

public import Oberwolfach.MarkedJointActiveWeightOrderedSeparateScales
public import Oberwolfach.MarkedActualParentPackingEventWithWeight
public import Oberwolfach.MarkedJointActualReferenceActiveLoadOrdered
public import Oberwolfach.MarkedJointActualReferenceActiveLoad
public import Oberwolfach.MarkedActualParentPackingEvent

@[expose] public section
/-! Reference, absorber, active local-load and parent packing-load estimates
on one retained outcome, with both weight families fixed beforehand. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_joint_actual_reference_active_parent_load_ordered_with_weights_separate_scales
    (r h k₀ Qpow:ℕ) (hr:2≤r) (hlen:r+4+1=(k₀+2)*2)
    (α ρ₀ sstar tstar kstar:ℝ)
    (hα:0<α) (hα1:α≤1) (hρ₀:0<ρ₀) (hsstar:0<sstar) (htstar:0<tstar) (htstar1:tstar≤1)
    (horder:tstar≤sstar) (hkstar:0<kstar)
    (hmargin:successorCycleRatio k₀+α/4≤1/2+α/2)
    :
    ∃ εAbs ζAbs δAbs:ℝ,0<εAbs ∧ 0<ζAbs ∧ 0<δAbs ∧
    ∃ βconfig:ℝ,0<βconfig ∧
    ∀ tolRef χActive Qref pstarRef ζActive τ tolLocal χLocal Qlocal ζLocal τParent tolParent χParent Qparent ζParent:ℝ,
    0<tolRef→0<χActive→0<pstarRef→pstarRef≤ρ₀*tstar/4→0<ζActive→
    0<τ→0<tolLocal→0<χLocal→0<ζLocal→0<τParent→0<tolParent→0<χParent→0<ζParent→
    ∃ βmax:ℝ,0<βmax ∧ ∀ εref δref χRef β ε:ℝ,
    0<εref→0<δref→0<χRef→0≤β→β≤βmax→β≤εref/4→0<ε→ε<1/4→
    ∀ (d:ℕ) (hd:2≤d),∃ m₀:ℕ,1≤m₀ ∧
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
    let ρParent:=markedVortexPermutation Q π hpres
    let Dparent:=fun i=>2*(Fintype.card (Z i):ℝ)/initialIndexDensity U D;
    ∃ weightParent:∀ i,(Fin (r+4+1)→W i)→ℝ,
    ∃ weight:∀ i,(Fin (r+4+1)→X i)→ℝ,
    (∀ i≤L,SuccessorSequenceWeightConditions (G.comap (fParent i)) (ρParent i) (3*d)
      (Dparent i) τParent (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weightParent i)) ∧
    (∀ i≤L+1,SuccessorSequenceWeightConditions (G.comap (f i)) (ρ i) (3*d)
      (Dactive i) τ (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weight i)) ∧
    ∀ (Γ Color:Type) [Fintype Γ] [Fintype Color] (s₀:ℝ) (hslo:sstar≤s₀) (hshi:s₀≤1/100),
    let dens:=initialIndexDensity U D
    let densities:=marked_seed_density_bounds (r+4) (by omega) dens s₀ ρ₀ sstar hρ₀ hsstar hρlo hρhi hslo hshi
    let p:=dens*s₀/2
    let kval:=p/((r+4:ℕ):ℝ);
    kstar≤p→kstar≤kval→
    ∀ (q:U→Γ→ℝ) (hq:∀ u a,0≤q u a) (hQ:∀ u,∑ a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a)) (a:Γ) (j:Color),
      (∀ u,q u a=s₀/((r+4:ℕ):ℝ))→(∀ u,s u j=s₀)→tstar≤s₀/((r+4:ℕ):ℝ)→
    let Eref:=MarkedReferenceActiveAbsorberProperty r h d (α/2) βconfig εref δref tolRef ζActive ζAbs tstar εAbs
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j
    let err:=χRef+2*χActive+2*(Fintype.card V:ℝ)^(-Qref)+2/(Fintype.card V:ℝ)^Qpow;
    1-χParent-(Fintype.card V:ℝ)^(-Qparent)-(χLocal+(Fintype.card V:ℝ)^(-Qlocal)+err)≤
      (rawMarkedRetentionLaw π d hd a p kval (densities.1.trans_le densities.2.1).le
        (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).probability
      (fun z=>(∀ i≤L,∀ δ:ℝ,0≤δ→∀ (DR:SimpleGraph (W i)) (DS:SimpleGraph (W i⊕Z i)),
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
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u))) ∧ Eref z) :=by
  obtain ⟨εAbs,ζAbs,δAbs,hεAbs,hζAbs,hδAbs,βconfig,hβconfig,hjoint⟩:=
    marked_joint_actual_reference_active_load_ordered_with_weight_separate_scales r h k₀ Qpow hr hlen α ρ₀ sstar tstar kstar
      hα hα1 hρ₀ hsstar htstar htstar1 horder hkstar hmargin
  refine ⟨εAbs,ζAbs,δAbs,hεAbs,hζAbs,hδAbs,βconfig,hβconfig,?_⟩
  intro tolRef χActive Qref pstarRef ζActive τ tolLocal χLocal Qlocal ζLocal τParent tolParent χParent Qparent ζParent
    htolRef hχActive hpstarRef hpstarRefBound hζActive hτ htolLocal hχLocal hζLocal hτParent htolParent hχParent hζParent
  obtain ⟨βjoint,hβjoint,hjoint⟩:=hjoint tolRef χActive Qref pstarRef ζActive τ tolLocal χLocal Qlocal ζLocal
      htolRef hχActive hpstarRef hpstarRefBound hζActive hτ htolLocal hχLocal hζLocal
  obtain ⟨βparent,hβparent,hparent⟩:=marked_actual_parent_packing_event_with_weight k₀ (r+4) hlen (by omega)
    α τParent ρ₀ sstar tstar tolParent χParent Qparent ζParent
    hα hτParent hρ₀ hsstar htstar htolParent hχParent hζParent hmargin
  let βmax:=min βjoint βparent
  have hβmax:0<βmax:=by dsimp [βmax];positivity
  refine ⟨βmax,hβmax,?_⟩
  intro εref δref χRef β ε hεref hδref hχRef hb hbmax hbε he he1 d hd
  have hbjoint:β≤βjoint:=hbmax.trans (min_le_left _ _)
  have hbparent:β≤βparent:=hbmax.trans (min_le_right _ _)
  obtain ⟨mJoint,hmJoint,hjoint⟩:=hjoint εref δref χRef β ε hεref hδref hχRef hb hbjoint hbε he he1 d hd
  obtain ⟨NParent,hNParent,hparent⟩:=hparent d hd
  obtain ⟨mParent,hmParent,hparent⟩:=hparent ε he he1.le
  let m₀:=max mJoint mParent
  have hm₀:1≤m₀:=hmJoint.trans (le_max_left _ _)
  refine ⟨m₀,hm₀,?_⟩
  intro size
  obtain ⟨a₀,b₀,e₀,hjoint⟩:=hjoint size
  refine ⟨a₀,b₀,e₀,?_⟩
  intro f₀
  obtain ⟨nJoint,hjoint⟩:=hjoint f₀
  refine ⟨max nJoint NParent,?_⟩
  intro V U _ _ _ _ G D m hreg hn hD hρlo hρhi hm hnBound hmn Q π hpres hshort L hL W Z A B X f g ρ Dactive pstarLocal fParent gParent ρParent Dparent
  letI : Nonempty V:=Fintype.card_pos_iff.mp hn
  have hnParent:NParent≤Fintype.card V:=(le_max_right _ _).trans hnBound
  have hnjoint:nJoint≤Fintype.card V:=(le_max_left _ _).trans hnBound
  have hmjoint:mJoint≤m:=(le_max_left _ _).trans hm
  have hmparent:mParent≤m:=(le_max_right _ _).trans hm
  obtain ⟨weight,hw,hweight⟩:=hjoint V U G D m hreg hn hD hρlo hρhi hmjoint hnjoint hmn Q π hpres hshort L hL
  obtain ⟨weightParent,hwParent,hweightParent⟩:=hparent V U G D m β Q hreg hn hnParent hD hρlo hρhi hb hbparent hmparent π hpres hshort L hL
  refine ⟨weightParent,weight,hwParent,hw,?_⟩
  intro Γ Color _ _ s₀ hslo hshi dens densities p kval hpmin hkmin q hq hQ s hs hS a j hq0 hs0 htlo Eref err
  let E:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a=>
    (∀ i≤L+1,MarkedLocalSpokeLoadsWithSpokes (G.comap (f i)) (ρ i) d (r+4) (Dactive i) p kval s₀ (weight i)
      (τ+tolLocal+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/pstarLocal^(2*(r+4)+1))*ζLocal)
      (rawMarkedRestrictPair (f i) (g i) z.1)
      (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u))) ∧ Eref z
  let errJoint:=χLocal+(Fintype.card V:ℝ)^(-Qlocal)+err
  have hjointProb:=hweight Γ Color s₀ hslo hshi hpmin hkmin q hq hQ s hs hS a j hq0 hs0 htlo
  have hExtra:1-errJoint≤(rawMarkedRetentionLaw π d hd a p kval (densities.1.trans_le densities.2.1).le
      (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).probability E:=by
    dsimp [errJoint]
    linarith
  exact hweightParent Γ Color s₀ hslo hshi q hq hQ s hs hS a j hq0 hs0 htlo E errJoint hExtra
end Oberwolfach
