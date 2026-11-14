module

public import Oberwolfach.MarkedSampleHubAndRowCovers
public import Oberwolfach.MarkedConfigurationsAfterPhysicalDeletion
public import Oberwolfach.MarkedPotentialPhysicalDeletion
public import Oberwolfach.MarkedSampleHubClassSizes

@[expose] public section

/-! A uniform deterministic deletion allowance for the actual sampled
hub-and-row construction. The same fixed profiles and root-omitted weights
suffice for every later physical deletion within the proved degree bounds.
No fresh random choice, changed coefficient or new good event is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 40000000
set_option maxRecDepth 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_sample_deep_cover_after_physical_deletion
    (r:ℕ) (hr:1≤r) (omega t rho gamma eta:ℝ)
    (ho:0<omega) (ht:0<t) (hrho:0<rho) (hrho1:rho≤1) (hg:0<gamma) (hg1:gamma≤1)
    (hst:(((r+1)+3:ℕ):ℝ)*t≤1) (heta:0<eta) (hetaSmall:eta≤t*(t*omega/2)/32)
    (β aLo B pstar:ℝ) (hβ:0<β) (hβt:β≤t/2) (haLo:0<aLo) (hB:0≤B) (hpstar:0<pstar):
    ∃ eps:ℝ,0<eps ∧ ∃ K:ℕ,0<K ∧ ∃ zeta:ℝ,0<zeta ∧
    ∃ θ:ℝ,0<θ ∧ ∃ delta:ℝ,0<delta ∧ ∀ d:ℕ,1≤d→∃ N:ℕ,1≤N ∧
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
    ∀ (D τ p k s₀:ℝ),(Fintype.card V:ℝ)/2≤D→D≤2*Fintype.card V→
    pstar≤p→pstar≤k→pstar≤s₀→p≤1→k≤1→s₀≤1→
    ∀ weight:(Fin (r+4+1)→V)→ℝ,SuccessorSequenceWeightConditions P π (3*d) D τ aLo B weight→
    MarkedLocalConfigurationsWithSpokes r P π d Finset.univ (2*β) (2*β) σ H→
    MarkedLocalSpokeLoadsWithSpokes P π d (r+4) D p k s₀ weight (θ/2) σ H→
    ∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
    (∀ x,(DR.degree x:ℝ)≤delta*Fintype.card V)→
    (∀ x,(DS.degree (Sum.inl x):ℝ)≤delta*Fintype.card V)→
    (∀ u,(DS.degree (Sum.inr u):ℝ)≤delta*Fintype.card V)→
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let tail:=fun e:E₀=>e.val.1
    let head:=fun e:E₀=>e.val.2
    let ktail:=fun e:E₁=>e.val.1
    let khead:=fun e:E₁=>e.val.2
    ∀ (F:Finset V),(∀ x,π x∈F↔x∈F)→((Fᶜ).card:ℝ)≤zeta*Fintype.card V→
    ∀ hHub:ℕ,(hHub:ℝ)≤zeta*Fintype.card V→
    ∀ u:Fin hHub→U,Function.Injective u→
    (∀ i x,¬(H' false x (u i)∧H' true x (u i)))→
    (∀ i x z,H' false x (u i)→H' true z (u i)→x≠π z)→
    (∀ i,Fintype.card (hubNeighbourClass (H' false) (H' true) (u i) false)=
      (r+4)*Fintype.card (hubNeighbourClass (H' false) (H' true) (u i) true))→
    (∀ i x,H' false x (u i)∨H' true x (u i)→x∈F)→
    ∀ (m:ℕ) (v:Fin m→V),Function.Injective v→(m:ℝ)≤zeta*Fintype.card V→(∀ i,v i∉F)→
    (∀ i u,¬(H' false (v i) u∧H' true (v i) u))→
    (∀ i,∀ a:E₀⊕E₁,Sum.elim head khead a=v i→Sum.elim tail ktail a∈F)→
    (∀ i,∀ a:E₀⊕E₁,Sum.elim tail ktail a=v i→Sum.elim head khead a∈F)→
    (∀ i,(Finset.univ.filter (fun a:E₀⊕E₁=>Sum.elim head khead a=v i)).card=
      (Finset.univ.filter (fun a:E₀⊕E₁=>Sum.elim tail ktail a=v i)).card)→
    (∀ i,(Finset.univ.filter (fun a:E₀⊕E₁=>Sum.elim head khead a=v i)).card=
      (Finset.univ.filter (fun z:V×U=>(H' false z.1 z.2∨H' true z.1 z.2)∧z.1=v i)).card)→
    (∀ i,(Finset.univ.filter (fun a:E₀⊕E₁=>Sum.elim head khead a=v i∧markedArcType a=true)).card=
      (Finset.univ.filter (fun z:V×U=>H' true z.1 z.2∧z.1=v i)).card)→
    let Y₀:=fun i=>Finset.univ.filter (H' false (v i))
    let Y₁:=fun i=>Finset.univ.filter (H' true (v i))
    let ain:=fun i=>markedEndpointTaggedArcEmbedding P π d Finset.univ true (v i) σ'
    let xout:=fun i=>markedEndpointTaggedArcEmbedding P π d Finset.univ false (v i) σ'
    (∀ i,Disjoint (Y₀ i∪Y₁ i) (Finset.univ.image u))→
    ∃ M:Finset (MarkedWheel tail head ktail khead (r+4) π (3*d) (H' false) (H' true)),
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
        (∀ x z,H' false x z∨H' true x z→markedStarResource T (Finset.univ.image u) (Sum.inr (x,z))→
          Sum.inr (x,z)∈M.biUnion markedWheelPhysicalResources) :=by
  obtain ⟨eps₀,heps₀,K,hK,zeta,hzeta,θ,hθ,hcover⟩:=marked_sample_hub_and_row_covers
    r hr omega t rho gamma eta ho ht hrho hrho1 hg hg1 hst heta hetaSmall β aLo B pstar hβ haLo hB hpstar
  let e:=min eps₀ (t/2)
  have he:0<e:=lt_min heps₀ (by positivity)
  have he0:e≤eps₀:=min_le_left _ _
  have het:e≤t/2:=min_le_right _ _
  let C:=5*((r+4:ℕ)+1:ℝ)^4*(2*B/pstar^(2*(r+4)+1))
  have hC:0≤C:=by dsimp [C];positivity
  let delta:=min (e/(8*(r+12:ℕ))) (min (β/(4*(r+6:ℕ))) (θ/(6*(C+1))))
  have hdelta:0<delta:=lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hde:delta*(8*(r+12:ℕ):ℝ)≤e:=
    (le_div_iff₀ (by positivity)).mp (min_le_left _ _)
  have hdb:delta*(4*(r+6:ℕ):ℝ)≤β:=
    (le_div_iff₀ (by positivity)).mp ((min_le_right _ _).trans (min_le_left _ _))
  have hdθ:delta*(6*(C+1))≤θ:=
    (le_div_iff₀ (by positivity)).mp ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨e/2,by positivity,K,hK,zeta,hzeta,θ,hθ,delta,hdelta,?_⟩
  intro d hd
  obtain ⟨N,hN,hcov⟩:=hcover d hd
  refine ⟨N,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hUn hU P π hdeg hparent q s g j hq hs σ H hrp hip
    D τ p k s₀ hDlo hDhi hp hk hs₀ hp1 hk1 hs₁ weight hw hconfigs hload DR DS hDR hDSr hDSc
  dsimp only
  intro F hF hFc hHub hhub u hu hdis hsep hratio hneigh m v hv hm hvF hdisRow hinc hout hdir hbal hmark hYavoid
  let n:=Fintype.card V
  have hnpos:0<n:=lt_of_lt_of_le Nat.zero_lt_one (hN.trans hn)
  have hnR:0<(n:ℝ):=Nat.cast_pos.mpr hnpos
  have hprof:=marked_neighbourhoods_after_physical_deletion P π d (r+12) Finset.univ Finset.univ
    (rho*(((r+4:ℕ):ℝ)*t)/2) (rho*t/2) q s g j ((e/2)*n) ((e/2)*n)
    (delta*n) (delta*n) (delta*n) (by positivity) (by positivity) (by positivity)
    σ H hrp hip DR DS hDR hDSr hDSc
  have hrowerr:(e/2)*n+(r+12:ℕ)*(delta*n+delta*n)≤e*n:=by
    have hh:=mul_le_mul_of_nonneg_right hde hnR.le
    have hp:0≤delta*(r+12:ℕ)*n:=by positivity
    nlinarith only [hh,hp]
  have hinderr:(e/2)*n+(r+12:ℕ)*(delta*n)≤e*n:=by
    have hh:=mul_le_mul_of_nonneg_right hde hnR.le
    have hp:0≤delta*(r+12:ℕ)*n:=by positivity
    nlinarith only [hh,hp]
  have hrp':MarkedRowsWithSpokes P π d (r+12) Finset.univ (rho*(((r+4:ℕ):ℝ)*t)/2) (rho*t/2)
      q s g j (e*n) (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes H DS):=by
    intro S T J hS hT hJ hinj
    exact (hprof.1 S T J hS hT hJ hinj).trans_le hrowerr
  have hip':MarkedIndicesWithSpokes π d (r+12) Finset.univ q s g j (e*n)
      (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes H DS):=by
    intro J hJ hsep
    exact (hprof.2 J hJ hsep).trans_le hinderr
  have hconfigs':=marked_local_configurations_after_physical_deletion r P π d (2*β) (2*β) delta delta
    σ H hconfigs DR DS hDR hDSc
  have hbc:β≤2*β-(r+5:ℕ)*(delta+delta):=by
    have hd0:=hdelta.le
    push_cast at hdb ⊢
    nlinarith only [hdb,hd0]
  have hbp:β≤2*β-(r+7:ℕ)*delta-(r+4:ℕ)*delta:=by
    have hd0:=hdelta.le
    push_cast at hdb ⊢
    nlinarith only [hdb,hd0]
  have hc':MarkedLocalConfigurationsWithSpokes r P π d Finset.univ β β
      (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes H DS):=by
    constructor
    · intro u
      exact (mul_le_mul_of_nonneg_right hbc (by positivity)).trans (hconfigs'.1 u)
    · intro u j x y hxy
      exact (mul_le_mul_of_nonneg_right hbp (by positivity)).trans (hconfigs'.2 u j x y hxy)
  have hloads':=marked_local_spoke_loads_after_physical_deletion P π d (r+4) (by omega) hnpos
    D τ aLo B hDlo hDhi p k s₀ pstar hpstar hp hk hs₀ hp1 hk1 hs₁ hB weight hw
    (θ/2) (delta*n) (delta*n) (by positivity) (by positivity) σ H hload DR DS hDR hDSr hDSc
  have hloaderr:θ/2+C*(2*(delta*n)+delta*n)/n≤θ:=by
    have heq:C*(2*(delta*n)+delta*n)/n=3*C*delta:=by field_simp;ring
    rw [heq]
    nlinarith only [hdθ,hdelta.le]
  have hl':MarkedLocalSpokeLoadsWithSpokes P π d (r+4) D p k s₀ weight θ
      (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes H DS):=by
    intro a
    exact (hloads' a).trans hloaderr
  have hcurrentSize (i:Fin hHub):β*n≤Fintype.card
      (hubNeighbourClass (markedDeletePhysicalSpokes H DS false) (markedDeletePhysicalSpokes H DS true) (u i) true):=
    (mul_le_mul_of_nonneg_right hβt hnR.le).trans
      (marked_sample_hub_class_lower P π d (r+12) (by omega) _ _ t e q s g j hq het
        (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes H DS) hrp' (u i))
  have hen:e*n≤eps₀*n:=mul_le_mul_of_nonneg_right he0 hnR.le
  exact hcov V U Γ Color hn hUn hU P π hdeg
    (fun x=>(hparent x).trans ((mul_le_mul_of_nonneg_right (by linarith only [he0,he]:e/2≤eps₀) hnR.le)))
    q s g j hq hs (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes H DS)
    (fun S T J hS hT hJ hinj=>(hrp' S T J hS hT hJ hinj).trans_le hen)
    (fun J hJ hsep=>(hip' J hJ hsep).trans_le hen)
    F hF hFc hHub hhub u hu hdis hsep hcurrentSize hratio hneigh
    D τ p k s₀ hDlo hDhi hp hk hs₀ hp1 hk1 hs₁ weight hw hc' hl'
    m v hv hm hvF hdisRow hinc hout hdir hbal hmark hYavoid

end Oberwolfach
