module

public import Oberwolfach.MarkedSampleRowCoversAfterHubRimsUniform
public import Oberwolfach.MarkedSampleHubCover
public import Oberwolfach.MarkedHubPackingSupport
public import Oberwolfach.MarkedPackingStageCombination
public import Oberwolfach.MarkedHubRowProtectedBounds
public import Oberwolfach.MarkedHubRowFullFreeDegrees
public import Oberwolfach.MarkedSampleRowCoverage

@[expose] public section

/-! The actual sampled deep-hub and deep-row stages from fixed parent,
profile, configuration and omitted-root weight estimates. All endpoint
pairings, path extension counts and hub factors are constructed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 30000000
set_option maxRecDepth 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_sample_hub_and_row_covers_uniform
    (r:ℕ) (hr:1≤r) (omega₀ t₀ rho₀ gamma eta:ℝ)
    (ho₀:0<omega₀) (ht₀:0<t₀) (ht₀1:t₀≤1) (hrho₀:0<rho₀) (hrho₀1:rho₀≤1)
    (hg:0<gamma) (hg1:gamma≤1) (heta:0<eta) (hetaSmall:eta≤t₀*(t₀*omega₀/2)/32)
    (β aLo B pstar:ℝ) (hβ:0<β) (haLo:0<aLo) (hB:0≤B) (hpstar:0<pstar):
    ∃ eps:ℝ,0<eps ∧ ∃ K:ℕ,0<K ∧ ∃ zeta:ℝ,0<zeta ∧
    ∃ θ:ℝ,0<θ ∧ ∀ d:ℕ,1≤d→∃ N:ℕ,1≤N ∧
    ∀ omega t rho:ℝ,omega₀≤omega → t₀≤t → rho₀≤rho → rho≤1 → (((r+1)+3:ℕ):ℝ)*t≤1 →
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    N≤Fintype.card V→(Fintype.card U:ℝ)≤Fintype.card V→ omega*Fintype.card V≤(Fintype.card U:ℝ)→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V),
    (∀ x,(1/2+gamma/2)*Fintype.card V≤(P.degree x:ℝ))→
    (∀ x,|(P.degree x:ℝ)-2*Fintype.card U/rho|≤eps*Fintype.card V)→
    ∀ (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color),
    (∀ u,q u g=t)→(∀ u,s u j=(((r+1)+3:ℕ):ℝ)*t)→
    ∀ (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop),
    MarkedRowsWithSpokes P π d ((r+1)+11) Finset.univ (rho*((((r+1)+3:ℕ):ℝ)*t)/2) (rho*t/2)
      q s g j (eps*Fintype.card V) σ H→
    MarkedIndicesWithSpokes π d ((r+1)+11) Finset.univ q s g j (eps*Fintype.card V) σ H→
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E₀=>e.val.1
    let head:=fun e:E₀=>e.val.2
    let ktail:=fun e:E₁=>e.val.1
    let khead:=fun e:E₁=>e.val.2
    ∀ (F:Finset V),(∀ x,π x∈F↔x∈F)→((Fᶜ).card:ℝ)≤zeta*Fintype.card V→
    ∀ hHub:ℕ,(hHub:ℝ)≤zeta*Fintype.card V→
    ∀ u:Fin hHub→U,Function.Injective u→
    (∀ i x,¬(H false x (u i)∧H true x (u i)))→
    (∀ i x z,H false x (u i)→H true z (u i)→x≠π z)→
    (∀ i,β*Fintype.card V≤Fintype.card (hubNeighbourClass (H false) (H true) (u i) true))→
    (∀ i,Fintype.card (hubNeighbourClass (H false) (H true) (u i) false)=
      (r+4)*Fintype.card (hubNeighbourClass (H false) (H true) (u i) true))→
    (∀ i x,H false x (u i)∨H true x (u i)→x∈F)→
    ∀ (D τ p k s₀:ℝ),(Fintype.card V:ℝ)/2≤D→D≤2*Fintype.card V→
    pstar≤p→pstar≤k→pstar≤s₀→p≤1→k≤1→s₀≤1→
    ∀ weight:(Fin (r+4+1)→V)→ℝ,SuccessorSequenceWeightConditions P π (3*d) D τ aLo B weight→
    MarkedLocalConfigurationsWithSpokes r P π d Finset.univ β β σ H→
    MarkedLocalSpokeLoadsWithSpokes P π d (r+4) D p k s₀ weight θ σ H→
    ∀ (m:ℕ) (v:Fin m→V),Function.Injective v→(m:ℝ)≤zeta*Fintype.card V→(∀ i,v i∉F)→
    (∀ i u,¬(H false (v i) u∧H true (v i) u))→
    (∀ i,∀ a:E₀⊕E₁,Sum.elim head khead a=v i→Sum.elim tail ktail a∈F)→
    (∀ i,∀ a:E₀⊕E₁,Sum.elim tail ktail a=v i→Sum.elim head khead a∈F)→
    (∀ i,(Finset.univ.filter (fun a:E₀⊕E₁=>Sum.elim head khead a=v i)).card=
      (Finset.univ.filter (fun a:E₀⊕E₁=>Sum.elim tail ktail a=v i)).card)→
    (∀ i,(Finset.univ.filter (fun a:E₀⊕E₁=>Sum.elim head khead a=v i)).card=
      (Finset.univ.filter (fun z:V×U=>(H false z.1 z.2∨H true z.1 z.2)∧z.1=v i)).card)→
    (∀ i,(Finset.univ.filter (fun a:E₀⊕E₁=>Sum.elim head khead a=v i∧markedArcType a=true)).card=
      (Finset.univ.filter (fun z:V×U=>H true z.1 z.2∧z.1=v i)).card)→
    let Y₀:=fun i=>Finset.univ.filter (H false (v i))
    let Y₁:=fun i=>Finset.univ.filter (H true (v i))
    let ain:=fun i=>markedEndpointTaggedArcEmbedding P π d Finset.univ true (v i) σ
    let xout:=fun i=>markedEndpointTaggedArcEmbedding P π d Finset.univ false (v i) σ
    (∀ i,Disjoint (Y₀ i∪Y₁ i) (Finset.univ.image u))→
    ∃ M:Finset (MarkedWheel tail head ktail khead (r+4) π (3*d) (H false) (H true)),
      (∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z)) ∧
      (∀ x,(spanningRestriction (markedPackingRimGraph M) F).degree x≤2*hHub+m*(4*(K+4))) ∧
      (∀ x∈F,(markedPackingRimGraph M).degree x≤2*hHub+m*(4*(K+4))+2*m) ∧
      (∀ x∈F,(Finset.univ.filter (markedPackingSpokes M x)).card≤hHub+m*(K+4)) ∧
      (∀ z∉Finset.univ.image u,(Finset.univ.filter (fun x=>markedPackingSpokes M x z)).card≤m*(r+5)) ∧
      (∀ (I:Finset V) (J:Finset U),Disjoint F I→(∀ x,π x∈I↔x∈I)→
        (∀ i,Disjoint (Y₀ i∪Y₁ i) J)→
        (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=∅) ∧
      (∀ W∈M,(W.2.val∈Finset.univ.image u∧markedWheelRows W⊆F)∨
        ∃ i,W.2.val∈Y₀ i∪Y₁ i∧markedWheelRows W⊆insert (v i) F∧v i∈markedWheelRows W) ∧
      ∀ T:Finset V,T⊆Finset.univ.image v→(∀ x,π x∈T↔x∈T)→
        (∀ a:E₀⊕E₁,markedStarResource T (Finset.univ.image u)
          (Sum.inl (markedPhysicalEdge tail head ktail khead π a))→
          Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈M.biUnion markedWheelPhysicalResources) ∧
        (∀ x z,H false x z∨H true x z→markedStarResource T (Finset.univ.image u) (Sum.inr (x,z))→
          Sum.inr (x,z)∈M.biUnion markedWheelPhysicalResources):=by
  obtain ⟨eps,heps,K,hK,zeta₀,hzeta₀,hrows⟩:=marked_sample_row_covers_after_hub_rims_uniform
    (r+1) (by omega) omega₀ t₀ rho₀ gamma eta ho₀ ht₀ ht₀1 hrho₀ hrho₀1 hg hg1 heta hetaSmall
  obtain ⟨θ,hθ,N₀,hN₀,hhubs⟩:=marked_sample_hub_cover r β aLo B pstar hβ haLo hB hpstar
  let zeta:=min zeta₀ (θ/2)
  have hzeta:0<zeta:=lt_min hzeta₀ (by positivity)
  have hz0:zeta≤zeta₀:=min_le_left _ _
  have hzθ:zeta≤θ/2:=min_le_right _ _
  refine ⟨eps,heps,K,hK,zeta,hzeta,θ,hθ,?_⟩
  intro d hd
  obtain ⟨N₁,hN₁,hrow⟩:=hrows d hd
  refine ⟨max N₀ N₁,hN₀.trans (le_max_left _ _),?_⟩
  intro omega t rho hω htlo hρ hrho1 hst
  intro V U Γ Color _ _ _ _ _ _ hn hUn hU P π hdeg hparent q s g j hq hs σ H hrp hip
  try dsimp only
  intro F hF hFc hHub hhub u hu hdis hsep hsize hratio hneigh D τ p k s₀ hDlo hDhi hp hk hs₀ hp1 hk1 hs₁
    weight hw hconfigs hload m v hv hm hvF hdisRow hinc hout hdir hbal hmark
  intro hYavoid
  have hn0:(0:ℝ)≤Fintype.card V:=Nat.cast_nonneg _
  have hsmall:(2*hHub:ℝ)≤θ*Fintype.card V:=by
    have hh:=hhub.trans (mul_le_mul_of_nonneg_right hzθ hn0)
    linarith only [hh]
  obtain ⟨M₀,hM₀,hMcover,hMdeg,hMunique,hMpairs⟩:=hhubs V U Γ Color
    ((le_max_left _ _).trans hn) hHub u hu hsmall P π d hd D τ p k s₀ hDlo hDhi hp hk hs₀ hp1 hk1 hs₁
    weight hw σ H hdis hsep hsize hratio hconfigs hload
  obtain ⟨hMhubs,hMrows,hMsupport⟩:=marked_hub_cover_support M₀ u hMcover F hF hneigh
  obtain ⟨C,hC,hcross,hCrim⟩:=hrow omega t rho hω htlo hρ hrho1 hst V U Γ Color ((le_max_right _ _).trans hn) hUn hU
    P π hdeg hparent q s g j hq hs σ H hrp hip F hF
    (hFc.trans (mul_le_mul_of_nonneg_right hz0 hn0)) hHub
    (hhub.trans (mul_le_mul_of_nonneg_right hz0 hn0)) (markedPackingRimGraph M₀) hMsupport
    (by intro x;exact_mod_cast hMdeg x) m v hv
    (hm.trans (mul_le_mul_of_nonneg_right hz0 hn0)) hvF hdisRow hinc hout hdir hbal hmark
  let Y:=fun i=>Finset.univ.filter (H false (v i))∪Finset.univ.filter (H true (v i))
  let required:=fun i=>markedRowRequiredResources
    (tail:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1) (head:=fun e=>e.val.2)
    (ktail:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1) (khead:=fun e=>e.val.2) (π:=π)
    (markedEndpointTaggedArcEmbedding P π d Finset.univ true (v i) σ)
    (markedEndpointTaggedArcEmbedding P π d Finset.univ false (v i) σ) (v i) (Y i)
  have hh:=marked_hub_row_stages_combine (by omega) (by omega) M₀ (Finset.univ.image u) hM₀ hMhubs
    C v F required Y hC hcross hCrim hYavoid
  obtain ⟨hbr,hbs,hbc⟩:=marked_hub_row_free_degree_bounds M₀ u hMhubs hMdeg C v F required Y hC
  let M:=M₀∪Finset.univ.biUnion C
  have hsupport:∀ W∈M,(W.2.val∈Finset.univ.image u∧markedWheelRows W⊆F)∨
        ∃ i,W.2.val∈Y i∧markedWheelRows W⊆insert (v i) F∧v i∈markedWheelRows W:=by
    intro W hW
    rcases Finset.mem_union.mp hW with hW|hW
    · exact Or.inl ⟨hMhubs W hW,hMrows W hW⟩
    · obtain ⟨i,_,hW⟩:=Finset.mem_biUnion.mp hW
      exact Or.inr ⟨i,(hC i).hubs W hW,(hC i).rows W hW,(hC i).root W hW⟩
  have hrowsAll:∀ W∈M,markedWheelRows W⊆F∪Finset.univ.image v:=by
    intro W hW x hx
    rcases hsupport W hW with ⟨_,hrows⟩|⟨i,_,hrows,_⟩
    · exact Finset.mem_union_left _ (hrows hx)
    · rcases Finset.mem_insert.mp (hrows hx) with he|he
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he.symm⟩)
      · exact Finset.mem_union_left _ he
  have hfull:=marked_hub_row_full_free_rim_degree M v F hF hrowsAll _ hbr
  refine ⟨M,hh.1,hbr,hfull,hbs,hbc,?_,hsupport,?_⟩
  · intro I J hFI hI hYJ
    exact marked_hub_row_avoids_inner (by omega) M₀ C v F I J required Y hC hMrows hFI hI hYJ
  · intro T hTv hT
    obtain ⟨hR,hS⟩:=marked_sample_row_covers_cover_star P π d (r+1) m K σ H F T v hTv hT C hC
    have hCM:(Finset.univ.biUnion C).biUnion markedWheelPhysicalResources⊆M.biUnion markedWheelPhysicalResources:=by
      intro e he
      obtain ⟨W,hW,he⟩:=Finset.mem_biUnion.mp he
      exact Finset.mem_biUnion.mpr ⟨W,Finset.mem_union_right _ hW,he⟩
    constructor
    · intro a ha
      exact hCM (hR a ha)
    · intro x z hx hs
      rcases hs with hs|hs
      · exact hCM (hS x z hx hs)
      · obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hs
        have he:Sum.inr (x,z)∈M₀.biUnion markedWheelPhysicalResources:=by
          rw [hMcover]
          apply Finset.mem_union_right
          apply Finset.mem_biUnion.mpr
          refine ⟨i,Finset.mem_univ _,?_⟩
          apply Finset.mem_image.mpr
          refine ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
          · simpa only [hi] using hx
          · rw [hi]
        exact hh.2 (Finset.mem_union_left _ he)

end Oberwolfach
