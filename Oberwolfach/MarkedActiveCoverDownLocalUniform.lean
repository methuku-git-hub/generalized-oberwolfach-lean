module

public import Oberwolfach.MarkedActiveCoverDownLocal
public import Oberwolfach.MarkedSampleActualBoundaryCompletionUniform

@[expose] public section
/-! The active cover-down construction, with its tolerances and order
threshold uniform over later actual spoke densities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 36000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_active_cover_down_local_uniform_spoke_density (α pA0:ℝ)
    (hα:0<α) (hαmax:α≤1) (hpA0:0<pA0) (hpA0max:pA0≤1/2):
    ∃ c₀:ℕ,∀ r:ℕ,2≤r→c₀≤r+5→∀ βA Lsp bminus bplus ωA hcutA δA:ℝ,
    0<βA→1≤Lsp→0<bminus→0<bplus→0<ωA→0<hcutA→0<δA→δA<1/4→
    ∃ ε η₀ δ₀ ξ:ℝ,0<ε∧0<η₀∧0<δ₀∧0<ξ∧
    ∀ βfree ν β aLo B pstar t₀ p₀ a gap omega:ℝ,
    0<βfree→0<ν→0<β→0<aLo→0≤B→0<pstar→0<t₀→0<p₀→p₀≤1→0<a→a≤1→0<gap→0<omega→ omega≤1→
    ∃ η ηEnd ζ pmax:ℝ,0<η∧0<ηEnd∧0<ζ∧0<pmax∧pmax≤1/8∧
    ∀ (p:ℝ) (hp:0<p) (hp1:p≤1),p≤pmax→∃ θ:ℝ,0<θ∧∀ d:ℕ,1≤d→∃ N:ℕ,1≤N∧
    ∀ t:ℝ,t₀≤t → ∀ (W V U Gamma Color J I:Type) [Fintype W] [LinearOrder W] [Fintype V] [LinearOrder V]
      [Fintype U] [DecidableEq U] [Fintype Gamma] [Fintype Color]
      [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I],
    N≤Fintype.card W→ omega*Fintype.card (V⊕U)≤(Fintype.card W:ℝ)→Fintype.card J≤(Fintype.card W)^2→
    ∀ (f:W↪oV) (ρ:Equiv.Perm W) (π:Equiv.Perm V),(∀ x,f (ρ x)=π (f x))→
    ∀ (P:SimpleGraph V) (D τweight pr kr sr:ℝ),
    (Fintype.card W:ℝ)/2≤D→D≤2*Fintype.card W→
    pstar≤pr→pstar≤kr→pstar≤sr→pr≤1→kr≤1→sr≤1→
    ∀ weight:(Fin (r+4+1)→W)→ℝ,SuccessorSequenceWeightConditions (P.comap f) ρ (3*d) D τweight aLo B weight→
    ∀ (σ:RawMarkedOutcome V U Gamma Color) (H:Bool→V→U→Prop) (u:J↪U) (root:I↪V) (Zinner:Finset U),
    (∀ j,u j∉Zinner)→(∀ i,root i∉Finset.univ.image f)→
    (∀ u v,¬(H false v u∧H true v u))→
    (∀ u v z,H false v u→H true z u→v≠π z)→
    ∀ (Q:U→Gamma→ℝ) (S:U→Color→ℝ) (g:Gamma) (c:Color),
    (∀ u,Q u g=t)→
    MarkedRowsWithSpokes (P.comap f) ρ d 1 Finset.univ pr kr Q S g c ((t/2)*Fintype.card W)
      (rawMarkedRestrictVertices f σ) (fun b x u=>H b (f x) u)→
    MarkedLocalConfigurationsWithSpokes r (P.comap f) ρ d Finset.univ β β
      (rawMarkedRestrictVertices f σ) (fun b x u=>H b (f x) u)→
    MarkedLocalSpokeLoadsWithSpokes (P.comap f) ρ d (r+4) D pr kr sr weight η
      (rawMarkedRestrictVertices f σ) (fun b x u=>H b (f x) u)→
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    let X:=Finset.univ.image f;
    ∀ h:ℕ,3≤h→∀ errR errI:ℝ,0≤errR→0≤errI→
      2*errR≤ηEnd*(a*Fintype.card (V⊕U))→2*errI≤ηEnd*(a*Fintype.card (V⊕U))→
    MarkedRowsWithSpokes P π d h X pr kr Q S g c errR σ H→
    MarkedIndicesWithSpokes π d h Zinner Q S g c errI σ H→
    ∀ w:Bool→ℝ,(∀ u∈Zinner,Q u g=w true)→(∀ u∈Zinner,S u c=w false)→
      (∀ e,p₀≤w e∧w e≤1)→
    let L:=fun (j:I×Fin 5)=>markedEndpointLabels P π d X
      (markedEndpointFiveRimType j.2,markedEndpointFiveIncoming j.2,root j.1) σ
    let T:=fun (j:I×Fin 5)=>Zinner.filter (H (markedEndpointFiveRootSpokeType j.2) (root j.1));
      (∀ j,a*Fintype.card (V⊕U)≤((L j).card:ℝ)∧a*Fintype.card (V⊕U)≤((T j).card:ℝ))→
      (∀ i,((markedEndpointLabels P π d X (true,false,root i) σ).card:ℝ)+
        gap*Fintype.card (V⊕U)≤(Zinner.filter (H false (root i))).card)→
      (∀ v∉X,∃ i,root i=v)→(∀ v∉Zinner,∃ j,u j=v)→
      MarkedBoundaryExtensionCounts tail head ktail khead (H false) (H true) X (β*Fintype.card (V⊕U))→
    ∀ (pA DA : ℝ),pA0≤pA → pA≤1/2 → 
    (Fintype.card V:ℝ)/2≤DA → DA≤2*Fintype.card V →
    (∀ x,|occurrenceDegree tail x-pA*DA|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree head x-pA*DA|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree ktail x-pA*DA/(r+4:ℝ)|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree khead x-pA*DA/(r+4:ℝ)|≤ε*Fintype.card V) →
    (∀ x y,x≠y → 4*α*pA^2*Fintype.card V≤
      ((Finset.univ.filter (fun z => (∃ e,tail e=x ∧ head e=z) ∧ (∃ e,tail e=z ∧ head e=y))).card:ℝ)) →
    (∀ S T : Finset V,(1-2*min (α/16) (pA/128))*Fintype.card V<(S.card:ℝ)+T.card →
      4*(α*pA/16)*Fintype.card V*min (S.card:ℝ) T.card≤
      ((Finset.univ.filter (fun e => tail e∈S ∧ head e∈T)).card:ℝ)) →
    (∀ C' : MarkedCycleTuple tail head ktail khead (r+4) π (3*d),
      4*βA*Fintype.card V≤(Fintype.card {u // MarkedHubCompatible (H false) (H true) C'.val u}:ℝ)) →
    ωA*Fintype.card V≤Fintype.card U → Fintype.card U≤Fintype.card V →
    ∀ (ps qs : Bool → U → ℝ) (δsp Dexc : ℝ),
    (∀ j,SparseIntersectionData (if j then (H true) else (H false)) (ps j) (qs j) Lsp δsp Dexc) →
    δsp+Dexc/(Fintype.card V:ℝ)+1/(Fintype.card U:ℝ)≤δ₀ →
    ∀ i : Bool → Fin (r+5),(∀ j,markedPositionType (i j)=j) →
    (∀ u u' : U,u≠u' → 4*βA*(Fintype.card V:ℝ)^(r+5)≤
      (Fintype.card (CommonMarkedCycle tail head ktail khead (r+4) π (3*d) (H false) (H true) u u'):ℝ)) →
    (∀ j,∀ Q : BipartiteFourCycle (if j then (H true) else (H false)),
      4*βA*(Fintype.card V:ℝ)^(r+4)≤
      (Fintype.card (CanonicalCommonMarkedPath tail head ktail khead (r+4) π (3*d) (H false) (H true) (i j)
        Q.val.1.1 Q.val.1.2 Q.val.2.1 Q.val.2.2):ℝ)) →
    ∀ ψ : MarkedWheel tail head ktail khead (r+4) π (3*d) (H false) (H true) → ℝ,
    (∀ e,|markedWheelRimLoad ψ e-1|≤η₀) →
    (∀ j v u,|markedSpokeResidual ψ j v u|≤η₀) →
    (∀ W,bminus/(Fintype.card V:ℝ)^(r+4)≤ψ W ∧ ψ W≤bplus/(Fintype.card V:ℝ)^(r+4)) →
    BipartiteLargeCut (occurrenceMultiplicity tail head) δA (2*hcutA) →
    BipartiteLargeCut (occurrenceMultiplicity ktail khead) δA (2*hcutA) →
    BipartiteLargeCut (relationMultiplicity (H false)) δA (2*hcutA) →
    BipartiteLargeCut (relationMultiplicity (H true)) δA (2*hcutA) →
    ( (ordinaryInnerVertices X Zinner).card:ℝ)≤ξ*Fintype.card V →
    (∀ x,π x∈X↔x∈X) →
    (∀ j x u,βfree*Fintype.card (V⊕U)≤((X.filter (fun z=>markedArcPresent tail head ktail khead j x z∧
      (if j then (H true) z u else (H false) z u))).card:ℝ)) →
    (∀ j x y u,x≠(if j then π y else y)→βfree*Fintype.card (V⊕U)≤
      ((X.filter (fun z=>markedArcPresent tail head ktail khead false x z∧
        markedArcPresent tail head ktail khead j z y∧(H false) z u)).card:ℝ)) →
    (∀ a:E⊕K,Sum.elim tail ktail a∉X→Sum.elim head khead a∉X→
      ¬PermutationClose π (3*d) (Sum.elim tail ktail a) (Sum.elim head khead a)) →
    (∀ a:E⊕K,Sum.elim tail ktail a∉X→Sum.elim head khead a∉X→
      βfree*Fintype.card (V⊕U)≤((Zinner.filter (fun u=>(H false) (Sum.elim tail ktail a) u∧
      (if markedArcType a then (H true) (Sum.elim head khead a) u else (H false) (Sum.elim head khead a) u))).card:ℝ)) →
    let a:=fun r j=>((markedBalanceTermSet tail head ktail khead (H false) (H true) r j).card:ℝ)
    let c:=fun r j=>(((markedBalanceTermSet tail head ktail khead (H false) (H true) r j).filter (fun e=>
      (if markedActiveAuxTail tail ktail (H false) (H true) e=r then markedActiveAuxHead head khead (H false) (H true) e
        else markedActiveAuxTail tail ktail (H false) (H true) e)∈ordinaryInnerVertices X Zinner)).card:ℝ);
    (∀ (v:V) (i:Fin 3),|markedSixDegreeBalance (r+4) (a (Sum.inl v)) i.castSucc|≤θ*Fintype.card V) →
    (∀ (v:V) (i:Fin 3),|markedSixDegreeBalance (r+4) (c (Sum.inl v)) i.castSucc|≤θ*Fintype.card V) →
    (∀ u,|markedSixDegreeBalance (r+4) (a (Sum.inr u)) 3|≤θ*Fintype.card V) →
    (∀ u,|markedSixDegreeBalance (r+4) (c (Sum.inr u)) 3|≤θ*Fintype.card V) →
    MarkedOutsideBalance tail head ktail khead (H true) Finset.univ
      (Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2)) (r+4) X Zinner→
    ∃ M:Finset (MarkedWheel tail head ktail khead (r+4) π (3*d) (H false) (H true)),
       (∀ W∈M,∀ W'∈M,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))∧
       (∀ v,((spanningRestriction (markedPackingRimGraph M) X).degree v:ℝ)≤ν*Fintype.card (V⊕U))∧
       (∀ v∈X,((Zinner.filter (markedPackingSpokes M v)).card:ℝ)≤ν*Fintype.card (V⊕U))∧
       (∀ u∈Zinner,((X.filter (fun v=>markedPackingSpokes M v u)).card:ℝ)≤ν*Fintype.card (V⊕U))∧
       (let A':=Finset.univ\M.biUnion markedWheelArcs
        let S':=(Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2))\M.biUnion markedWheelSpokePairs
        (∀ a∈A',Sum.elim tail ktail a∈X∧Sum.elim head khead a∈X)∧
          (∀ s∈S',s.1∈X∧s.2∈Zinner)∧
          (A'.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S'.image Sum.inr)=
            (Finset.univ.image (fun a:E⊕K=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪
              (Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2)).image Sum.inr)\
              M.biUnion markedWheelPhysicalResources):=by
  obtain ⟨c₀,hc₀⟩:=marked_sampled_approximate_outside_cover_ordered α pA0 hα hαmax hpA0 hpA0max
  refine ⟨c₀,?_⟩
  intro r hr hrc βA Lsp bminus bplus ωA hcutA δA hβA hL hbm hbp hωA hhcutA hδA hδAmax
  obtain ⟨ε,η₀,δ₀,ξ,hε,hη₀,hδ₀,hξ,hApprox⟩:=hc₀ r hr hrc βA Lsp bminus bplus ωA hcutA δA
    hβA hL hbm hbp hωA hhcutA hδA hδAmax
  refine ⟨ε,η₀,δ₀,ξ,hε,hη₀,hδ₀,hξ,?_⟩
  intro βfree ν β aLo B pstar t₀ p₀ a gap omega hβfree hν hβ haLo hB hpstar ht₀ hp₀ hp₀1 ha ha1 hgap homega homega1
  let q:ℕ:=1
  obtain ⟨pAmax,hpAmax,hpAmax1,hAmax⟩:=hApprox βfree 1 hβfree (by norm_num) q
  obtain ⟨η,ηEnd,ζ,pC,hη,hηEnd,hζ,hpC,hpC8,hCmax⟩:=
    marked_sample_actual_boundary_completion_local_uniform r (by omega) ν hν β aLo B pstar t₀ p₀ a gap omega
      hβ haLo hB hpstar ht₀ hp₀ hp₀1 ha ha1 hgap homega homega1
  refine ⟨η,ηEnd,ζ,min pAmax pC,hη,hηEnd,hζ,lt_min hpAmax hpC,
    (min_le_right _ _).trans hpC8,?_⟩
  intro p hp hp1 hpp
  obtain ⟨θ,hθ,hAp⟩:=hAmax p hp (hpp.trans (min_le_left _ _))
  refine ⟨θ,hθ,?_⟩
  intro d hd
  obtain ⟨NA,hNA⟩:=hAp (3*d) (by omega)
  obtain ⟨NC,hNC1,hNC⟩:=hCmax d p hp hp1 (hpp.trans (min_le_right _ _)) q
  refine ⟨max NA (max NC 16),by omega,?_⟩
  intro t ht W V U Gamma Color J I _ _ _ _ _ _ _ _ _ _ _ _ hn hWlo hJ f ρ π hf P D τweight pr kr sr
    hDlo hDhi hpr hkr hsr hpr1 hkr1 hsr1 weight hw σ₀ H u root Zinner hu hroot hdtypes hsep
    Q S g c hQ hrows hconfigs hload E K tail head ktail khead X
    h hh errR errI heR heI heRsmall heIsmall hrowEnd hidxEnd w hQw hSw hwprob L₀ T hsize hgapParent
    hroots hhubs Qext pA DA hpA hpAmax' hDAlo hDAhi hdo hdi hdko hdki htwo hcut hhub hωn huV
    ps qs δsp Dexc hdata hsmall i hipos hcommon hpaths ψ hRerr hSerr hψ hcut0 hcutK hcutH0 hcutHK
    hinnerSize hX hstep hjoin hsepOutside hhubsOutside a₀ c₁ ha₀ hc₁ hau hcu hdiv
  have hWV:Fintype.card W≤Fintype.card V:=Fintype.card_le_of_injective f f.injective
  have hVn:Fintype.card V≤Fintype.card (V⊕U):=by simp only [Fintype.card_sum];omega
  have hAE:=hNA V E K U tail head ktail khead π (markedSampleArc_physical_injective P π (3*d) _)
    pA DA hpA hpAmax' (by omega) hDAlo hDAhi hdo hdi hdko hdki htwo hcut
    (H false) (H true) (fun v u=>hdtypes u v) hhub hωn huV ps qs δsp Dexc hdata hsmall i hipos
    hcommon hpaths ψ hRerr hSerr hψ hcut0 hcutK hcutH0 hcutHK X Zinner hinnerSize hX
    hstep hjoin hsepOutside hhubsOutside ha₀ hc₁ hau hcu hp.le hp1
  have hCE:=hNC t ht W V U Gamma Color J I (by omega) hWlo hJ f ρ π hf P D τweight pr kr sr
    hDlo hDhi hpr hkr hsr hpr1 hkr1 hsr1 weight hw σ₀ H u root Zinner hu hroot hdtypes hsep
    Q S g c hQ hrows hconfigs hload h hh errR errI heR heI heRsmall heIsmall
    hrowEnd hidxEnd w hQw hSw hwprob hsize hgapParent hroots hhubs Qext hd
  rw [sub_sub] at hCE
  let Good:Prop:=∃ M:Finset (MarkedWheel tail head ktail khead (r+4) π (3*d) (H false) (H true)),
       (∀ W∈M,∀ W'∈M,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))∧
       (∀ v,((spanningRestriction (markedPackingRimGraph M) X).degree v:ℝ)≤ν*Fintype.card (V⊕U))∧
       (∀ v∈X,((Zinner.filter (markedPackingSpokes M v)).card:ℝ)≤ν*Fintype.card (V⊕U))∧
       (∀ u∈Zinner,((X.filter (fun v=>markedPackingSpokes M v u)).card:ℝ)≤ν*Fintype.card (V⊕U))∧
       (let A':=Finset.univ\M.biUnion markedWheelArcs
        let S':=(Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2))\M.biUnion markedWheelSpokePairs
        (∀ a∈A',Sum.elim tail ktail a∈X∧Sum.elim head khead a∈X)∧
          (∀ s∈S',s.1∈X∧s.2∈Zinner)∧
          (A'.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S'.image Sum.inr)=
            (Finset.univ.image (fun a:E⊕K=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪
              (Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2)).image Sum.inr)\
              M.biUnion markedWheelPhysicalResources)
  change Good
  suffices hgood:1-1/(Fintype.card W:ℝ)^q-7/(Fintype.card (V⊕U):ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)).probability (fun _=>Good) by
    have hW16:(16:ℝ)≤Fintype.card W:=by exact_mod_cast (show 16≤Fintype.card W by omega)
    have hn16:(16:ℝ)≤Fintype.card (V⊕U):=hW16.trans (Nat.cast_le.mpr (hWV.trans hVn))
    have hwdiv:1/(Fintype.card W:ℝ)≤1/16:=div_le_div_of_nonneg_left (by norm_num) (by norm_num) hW16
    have hndiv:7/(Fintype.card (V⊕U):ℝ)≤7/16:=div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn16
    have hpos:0<1-1/(Fintype.card W:ℝ)^q-7/(Fintype.card (V⊕U):ℝ)^q:=by
      simp only [q,pow_one]
      linarith
    by_contra hnot
    simp only [FiniteLaw.probability,hnot,ite_false,Finset.sum_const_zero] at hgood
    linarith
  have hboth:=finiteLaw_two_events_lower _ _ _ _ _ hAE hCE
  apply le_trans (b:=1-4/(Fintype.card (V⊕U):ℝ)^q-(1/(Fintype.card W:ℝ)^q+3/(Fintype.card (V⊕U):ℝ)^q))
    (by ring_nf;exact le_rfl)
  apply hboth.trans
  apply finiteLaw_probability_mono
  intro σb hσ
  change Good
  obtain ⟨Mr,hM₀,haux,hphysical,hinner,hreserved,hleft,M₁,hM₁,hdisjoint,houtsideR,houtsideS,hcover,hcoverν⟩:=hσ.1
  let PE:=fun e:E=>¬markedBoundaryRimAllowed π X σb false (tail e) (head e)
  let PK:=fun e:K=>¬markedBoundaryRimAllowed π X σb true (ktail e) (khead e)
  let M₀:=Mr.image (markedWheelToLarger (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
    (m:=r+4) (π:=π) (b:=3*d) PE PK
    (fun (x:V) (u:U) (h:H false x u∧¬markedBoundarySpokeAllowed X Zinner σb x u)=>h.1)
    (fun (x:V) (u:U) (h:H true x u∧¬markedBoundarySpokeAllowed X Zinner σb x u)=>h.1))
  have hleft':∀ x,(((ordinaryBoundaryGraph (markedSampleArcSetGraph P π d σ₀ Finset.univ)
        (fun x u=>H false x u∨H true x u) X Zinner\
        retainedGraph (ordinaryBoundaryGraph (markedSampleArcSetGraph P π d σ₀ Finset.univ)
          (fun x u=>H false x u∨H true x u) X Zinner) σb)\
        ordinaryPhysicalGraph (markedPackingRimGraph M₀) (markedPackingSpokes M₀)).degree x:ℝ)≤p^9*Fintype.card (V⊕U):=by
    intro x
    have hs:=mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hVn) (pow_nonneg hp.le 9)
    apply le_trans (b:=p^9*Fintype.card V) _ hs
    convert hleft x using 1 <;> congr!
  have hcover':∀ x,((ordinaryPhysicalGraph (markedPackingRimGraph M₁) (markedPackingSpokes M₁)).degree x:ℝ)≤p^3*Fintype.card (V⊕U):=by
    intro x
    exact (hcover x).trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hVn) (pow_nonneg hp.le 3))
  obtain ⟨N,hN,hrest⟩:=hσ.2 M₀ M₁ hM₀ hM₁ hdisjoint.symm hinner houtsideR houtsideS hdiv
    (by convert hreserved using 1 <;> congr!) hleft' hcover'
  exact ⟨M₀∪M₁∪N,hrest⟩
end Oberwolfach
