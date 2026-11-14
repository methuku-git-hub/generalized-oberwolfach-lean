module

public import Oberwolfach.MarkedActiveGlobalConditions

@[expose] public section

/-! The actual active cover-down constructor with its global inputs grouped
as one explicit predicate. No packing, selected factor or endpoint pairing
is an assumption: the original constructor supplies all of them. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_active_cover_down_global_conditions (α pA0:ℝ)
    (hα:0<α) (hαmax:α≤1) (hpA0:0<pA0) (hpA0max:pA0≤1/2):
    ∃ c₀:ℕ,∀ r:ℕ,2≤r→c₀≤r+5→∀ βA Lsp bminus bplus ωA hcutA δA:ℝ,
    0<βA→1≤Lsp→0<bminus→0<bplus→0<ωA→0<hcutA→0<δA→δA<1/4→
    ∃ ε η₀ δ₀ ξ:ℝ,0<ε∧0<η₀∧0<δ₀∧0<ξ∧
    ∀ βfree ν β aLo B pstar t p₀ a gap omega:ℝ,
    0<βfree→0<ν→0<β→0<aLo→0≤B→0<pstar→0<t→0<p₀→p₀≤1→0<a→a≤1→0<gap→0<omega→ omega≤1→
    ∃ η ηEnd ζ pmax:ℝ,0<η∧0<ηEnd∧0<ζ∧0<pmax∧pmax≤1/8∧
    ∀ (p:ℝ) (hp:0<p) (hp1:p≤1),p≤pmax→∃ θ:ℝ,0<θ∧∀ d:ℕ,1≤d→∃ N:ℕ,1≤N∧
    ∀ (W V U Gamma Color J I:Type) [Fintype W] [LinearOrder W] [Fintype V] [LinearOrder V]
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
    ∀ (pA DA:ℝ),pA0≤pA→pA≤1/2→
    MarkedActiveGlobalConditions tail head ktail khead π d r (H false) (H true)
      pA DA α βA Lsp bminus bplus ωA ε η₀ δ₀ δA hcutA→
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
              M.biUnion markedWheelPhysicalResources) :=by
  obtain ⟨c₀,hall⟩:=marked_active_cover_down_local α pA0 hα hαmax hpA0 hpA0max
  refine ⟨c₀,?_⟩
  intro r hr hrc βA Lsp bminus bplus ωA hcutA δA hβA hL hbm hbp hωA hhcutA hδA hδAmax
  obtain ⟨ε,η₀,δ₀,ξ,hε,hη₀,hδ₀,hξ,hall⟩:=hall r hr hrc βA Lsp bminus bplus ωA hcutA δA
    hβA hL hbm hbp hωA hhcutA hδA hδAmax
  refine ⟨ε,η₀,δ₀,ξ,hε,hη₀,hδ₀,hξ,?_⟩
  intro βfree ν β aLo B pstar t p₀ a gap omega hβfree hν hβ haLo hB hpstar ht hp₀ hp₀1 ha ha1 hgap homega homega1
  obtain ⟨η,ηEnd,ζ,pmax,hη,hηEnd,hζ,hpmax,hpmax8,hall⟩:=hall βfree ν β aLo B pstar t p₀ a gap omega
    hβfree hν hβ haLo hB hpstar ht hp₀ hp₀1 ha ha1 hgap homega homega1
  refine ⟨η,ηEnd,ζ,pmax,hη,hηEnd,hζ,hpmax,hpmax8,?_⟩
  intro p hp hp1 hpp
  obtain ⟨θ,hθ,hall⟩:=hall p hp hp1 hpp
  refine ⟨θ,hθ,?_⟩
  intro d hd
  obtain ⟨N,hN,hall⟩:=hall d hd
  refine ⟨N,hN,?_⟩
  intro W V U Gamma Color J I _ _ _ _ _ _ _ _ _ _ _ _ hn hWlo hJ f ρ π hf P D τweight pr kr sr
    hDlo hDhi hpr hkr hsr hpr1 hkr1 hsr1 weight hw σ₀ H u root Zinner hu hroot hdtypes hsep
    Q S g c hQ hrows hconfigs hload E K tail head ktail khead X
    h hh errR errI heR heI heRsmall heIsmall hrowEnd hidxEnd w hQw hSw hwprob L₀ T hsize hgapParent
    hroots hhubs Qext pA DA hpA hpAmax' hglobal
    hinnerSize hX hstep hjoin hsepOutside hhubsOutside a₀ c₁ ha₀ hc₁ hau hcu hdiv
  obtain ⟨ps,qs,δsp,Dexc,hdata,hsmall⟩:=hglobal.spoke_intersections
  obtain ⟨ψ,hRerr,hSerr,hψ⟩:=hglobal.seed_weights
  exact hall W V U Gamma Color J I hn hWlo hJ f ρ π hf P D τweight pr kr sr
    hDlo hDhi hpr hkr hsr hpr1 hkr1 hsr1 weight hw σ₀ H u root Zinner hu hroot hdtypes hsep
    Q S g c hQ hrows hconfigs hload h hh errR errI heR heI heRsmall heIsmall hrowEnd hidxEnd
    w hQw hSw hwprob hsize hgapParent hroots hhubs Qext pA DA hpA hpAmax'
    hglobal.degree_lower hglobal.degree_upper hglobal.ordinary_out hglobal.ordinary_in
    hglobal.marked_out hglobal.marked_in hglobal.two_step hglobal.ordinary_cut hglobal.compatible_hubs
    hglobal.hubs_lower hglobal.hubs_upper ps qs δsp Dexc hdata hsmall
    (fun j=>(markedRootOrder (r+4) j).symm 0) (markedRootOrder_type (r+4) (by omega))
    hglobal.common_cycles hglobal.common_paths ψ hRerr hSerr hψ
    hglobal.ordinary_correction_cut hglobal.marked_correction_cut hglobal.ordinary_spoke_cut hglobal.marked_spoke_cut
    hinnerSize hX hstep hjoin hsepOutside hhubsOutside ha₀ hc₁ hau hcu hdiv

end Oberwolfach
