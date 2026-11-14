module

public import Oberwolfach.MarkedJointActualReferenceActiveParentLoad
public import Oberwolfach.MarkedReferenceExplicitFailureBudget

@[expose] public section
/-! One positive-mass outcome for the reference, absorber, active local-load
and adaptive parent packing-load estimates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_joint_actual_reference_active_parent_load_witness
    (r h k₀:ℕ) (hr:2≤r) (hlen:r+4+1=(k₀+2)*2)
    (α ρ₀ sstar tstar kstar tolRef pstarRef ζActive τ tolLocal ζLocal τParent tolParent ζParent:ℝ)
    (hα:0<α) (hα1:α≤1) (hρ₀:0<ρ₀) (hsstar:0<sstar) (htstar:0<tstar) (htstar1:tstar≤1)
    (horder:tstar≤sstar) (hkstar:0<kstar)
    (hmargin:successorCycleRatio k₀+α/4≤1/2+α/2)
    (htolRef:0<tolRef) (hpstarRef:0<pstarRef)
    (hpstarRefBound:pstarRef≤ρ₀*tstar/4) (hζActive:0<ζActive)
    (hτ:0<τ) (htolLocal:0<tolLocal) (hζLocal:0<ζLocal)
    (hτParent:0<τParent) (htolParent:0<tolParent) (hζParent:0<ζParent):
    ∃ εAbs ζAbs δAbs:ℝ,0<εAbs ∧ 0<ζAbs ∧ 0<δAbs ∧
    ∃ βconfig βmax:ℝ,0<βconfig ∧ 0<βmax ∧ ∀ size:ℕ,∃ a₀ b₀ e₀:ℕ,
    ∀ εref δref β ε:ℝ,
    0<εref→0<δref→0≤β→β≤βmax→β≤εref/4→0<ε→ε<1/4→
    ∀ (f₀ d:ℕ) (hd:2≤d),∃ m₀:ℕ,1≤m₀ ∧
    ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ),G.IsRegularOfDegree D→∀ (hn:0<Fintype.card V),
    (1/2+α)*Fintype.card V≤(D:ℝ)→∀ (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1),
    m₀≤m→m≤Fintype.card V→∀ (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
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
    ∃ z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a,
      0<(rawMarkedRetentionLaw π d hd a p kval (densities.1.trans_le densities.2.1).le
        (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).mass z ∧
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
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u))) ∧ Eref z :=by
  obtain ⟨εAbs,ζAbs,δAbs,hεAbs,hζAbs,hδAbs,βconfig,βmax,hβconfig,hβmax,hbase⟩:=
    marked_joint_actual_reference_active_parent_load r h k₀ 1 hr hlen α ρ₀ sstar tstar kstar
      tolRef (1/100) 1 pstarRef ζActive τ tolLocal (1/100) 1 ζLocal τParent tolParent (1/100) 1 ζParent
      hα hα1 hρ₀ hsstar htstar htstar1 horder hkstar hmargin htolRef (by norm_num)
      hpstarRef hpstarRefBound hζActive hτ htolLocal (by norm_num) hζLocal hτParent htolParent (by norm_num) hζParent
  refine ⟨εAbs,ζAbs,δAbs,hεAbs,hζAbs,hδAbs,βconfig,βmax,hβconfig,hβmax,?_⟩
  intro size
  obtain ⟨a₀,b₀,e₀,hbase⟩:=hbase size
  refine ⟨a₀,b₀,e₀,?_⟩
  intro εref δref β ε hεref hδref hb hbmax hbε he he1 f₀ d hd
  obtain ⟨mBase,hmBase,hbase⟩:=hbase εref δref (1/100) β ε hεref hδref (by norm_num) hb hbmax hbε he he1 f₀ d hd
  refine ⟨max mBase 16,hmBase.trans (le_max_left _ _),?_⟩
  intro V U _ _ _ _ G D m hreg hn hD hρlo hρhi hm hmn Q π hpres hshort L hL W Z A B X f g ρ Dactive pstarLocal fParent gParent ρParent Dparent
  have hmBase':mBase≤m:=(le_max_left _ _).trans hm
  have hn16:16≤Fintype.card V:=(le_max_right _ _).trans (hm.trans hmn)
  obtain ⟨weightParent,weight,hweight⟩:=hbase V U G D m hreg hn hD hρlo hρhi hmBase' hmn Q π hpres hshort L hL
  refine ⟨weightParent,weight,?_⟩
  intro Γ Color _ _ s₀ hslo hshi dens densities p kval hpmin hkmin q hq hQ s hs hS a j hq0 hs0 htlo Eref
  letI : Nonempty V:=Fintype.card_pos_iff.mp hn
  have hprob:=hweight Γ Color s₀ hslo hshi hpmin hkmin q hq hQ s hs hS a j hq0 hs0 htlo
  let μ:=rawMarkedRetentionLaw π d hd a p kval (densities.1.trans_le densities.2.1).le
    (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS
  let E:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a=>
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
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u))) ∧ Eref z
  have hnpos:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hpow:(Fintype.card V:ℝ)^(-(1:ℝ))=1/(Fintype.card V:ℝ):=by
    rw [Real.rpow_neg hnpos.le,Real.rpow_one,one_div]
  have hbound:1-(1/10:ℝ)-5*(Fintype.card V:ℝ)^(-(1:ℝ))-9*(Fintype.card V:ℝ)^(-(1:ℝ))≤μ.probability E:=by
    change 1-(1/100:ℝ)-(Fintype.card V:ℝ)^(-(1:ℝ))-((1/100:ℝ)+(Fintype.card V:ℝ)^(-(1:ℝ))+((1/100:ℝ)+2*(1/100:ℝ)+2*(Fintype.card V:ℝ)^(-(1:ℝ))+2/(Fintype.card V:ℝ)^1))≤μ.probability E at hprob
    rw [hpow] at hprob ⊢
    have hnonneg:0≤1/(Fintype.card V:ℝ):=by positivity
    simp only [pow_one] at hprob
    have htwo:(2:ℝ)/(Fintype.card V:ℝ)=2*(1/(Fintype.card V:ℝ)):=by ring
    rw [htwo] at hprob
    linarith
  obtain ⟨z,hz,hpos⟩:=marked_reference_explicit_positive_mass μ E (Fintype.card V) hn16 hbound
  exact ⟨z,hpos,hz.1,hz.2.1,hz.2.2⟩
end Oberwolfach
