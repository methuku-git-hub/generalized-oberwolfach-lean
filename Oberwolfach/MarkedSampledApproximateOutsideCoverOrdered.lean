module

public import Oberwolfach.MarkedComplementBoundaryRemainder
public import Oberwolfach.MarkedSampledComplementApproximation
public import Oberwolfach.MarkedSampledOutsideCompletion
public import Oberwolfach.MarkedComplementInnerExclusion
public import Oberwolfach.TwoCommonEvents

@[expose] public section

/-! Construct both earlier packings on one original boundary sample.
The approximate packing uses wheel parameter (l+3)+1=l+4, exactly the
parameter of the outside completion. The inner-set allowance is fixed before the extension density on that inner set.
The original typed occurrence maps
and physical resources are preserved when the first packing is lifted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_sampled_approximate_outside_cover_ordered (α p₀ : ℝ)
    (hα : 0<α) (hαmax : α≤1) (hp₀ : 0<p₀) (hp₀max : p₀≤1/2) :
    ∃ c₀ : ℕ,∀ l : ℕ,2≤l → c₀≤l+5 → ∀ β L bminus bplus ω h δ : ℝ,
    0<β → 1≤L → 0<bminus → 0<bplus → 0<ω → 0<h → 0<δ → δ<1/4 →
    ∃ ε η₀ δ₀ ξ:ℝ,0<ε ∧ 0<η₀ ∧ 0<δ₀ ∧ 0<ξ ∧
    ∀ βfree ν:ℝ,0<βfree → 0<ν → ∀ q:ℕ,
    ∃ τ₀:ℝ,0<τ₀ ∧ τ₀≤1/2 ∧
    ∀ (τ:ℝ),0<τ → τ≤τ₀ → ∃ θ:ℝ,0<θ ∧ ∀ b:ℕ,1≤b → ∃ n₀:ℕ,
    ∀ (V E K U : Type)
      [Fintype V] [Fintype E] [Fintype K] [Fintype U] [DecidableEq V] [DecidableEq U],
    ∀ (tail head : E → V) (ktail khead : K → V) (π : Equiv.Perm V),
    Function.Injective (markedPhysicalEdge tail head ktail khead π) →
    ∀ (p D : ℝ),p₀≤p → p≤1/2 → n₀≤Fintype.card V →
    (Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
    (∀ x,|occurrenceDegree tail x-p*D|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree head x-p*D|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree ktail x-p*D/(l+4:ℝ)|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree khead x-p*D/(l+4:ℝ)|≤ε*Fintype.card V) →
    (∀ x y,x≠y → 4*α*p^2*Fintype.card V≤
      ((Finset.univ.filter (fun z => (∃ e,tail e=x ∧ head e=z) ∧ (∃ e,tail e=z ∧ head e=y))).card:ℝ)) →
    (∀ S T : Finset V,(1-2*min (α/16) (p/128))*Fintype.card V<(S.card:ℝ)+T.card →
      4*(α*p/16)*Fintype.card V*min (S.card:ℝ) T.card≤
      ((Finset.univ.filter (fun e => tail e∈S ∧ head e∈T)).card:ℝ)) →
    ∀ H₀ Hₖ : V → U → Prop,
    (∀ v u,¬(H₀ v u ∧ Hₖ v u)) →
    (∀ C' : MarkedCycleTuple tail head ktail khead (l+4) π b,
      4*β*Fintype.card V≤(Fintype.card {u // MarkedHubCompatible H₀ Hₖ C'.val u}:ℝ)) →
    ω*Fintype.card V≤Fintype.card U → Fintype.card U≤Fintype.card V →
    ∀ (ps qs : Bool → U → ℝ) (δsp Dexc : ℝ),
    (∀ j,SparseIntersectionData (if j then Hₖ else H₀) (ps j) (qs j) L δsp Dexc) →
    δsp+Dexc/(Fintype.card V:ℝ)+1/(Fintype.card U:ℝ)≤δ₀ →
    ∀ i : Bool → Fin (l+5),(∀ j,markedPositionType (i j)=j) →
    (∀ u u' : U,u≠u' → 4*β*(Fintype.card V:ℝ)^(l+5)≤
      (Fintype.card (CommonMarkedCycle tail head ktail khead (l+4) π b H₀ Hₖ u u'):ℝ)) →
    (∀ j,∀ Q : BipartiteFourCycle (if j then Hₖ else H₀),
      4*β*(Fintype.card V:ℝ)^(l+4)≤
      (Fintype.card (CanonicalCommonMarkedPath tail head ktail khead (l+4) π b H₀ Hₖ (i j)
        Q.val.1.1 Q.val.1.2 Q.val.2.1 Q.val.2.2):ℝ)) →
    ∀ ψ : MarkedWheel tail head ktail khead (l+4) π b H₀ Hₖ → ℝ,
    (∀ e,|markedWheelRimLoad ψ e-1|≤η₀) →
    (∀ j v u,|markedSpokeResidual ψ j v u|≤η₀) →
    (∀ W,bminus/(Fintype.card V:ℝ)^(l+4)≤ψ W ∧ ψ W≤bplus/(Fintype.card V:ℝ)^(l+4)) →
    BipartiteLargeCut (occurrenceMultiplicity tail head) δ (2*h) →
    BipartiteLargeCut (occurrenceMultiplicity ktail khead) δ (2*h) →
    BipartiteLargeCut (relationMultiplicity H₀) δ (2*h) →
    BipartiteLargeCut (relationMultiplicity Hₖ) δ (2*h) →
    ∀ (X:Finset V) (Z:Finset U),( (ordinaryInnerVertices X Z).card:ℝ)≤ξ*Fintype.card V →
    (∀ x,π x∈X↔x∈X) →
    (∀ j x u,βfree*Fintype.card (V⊕U)≤((X.filter (fun z=>markedArcPresent tail head ktail khead j x z∧
      (if j then Hₖ z u else H₀ z u))).card:ℝ)) →
    (∀ j x y u,x≠(if j then π y else y)→βfree*Fintype.card (V⊕U)≤
      ((X.filter (fun z=>markedArcPresent tail head ktail khead false x z∧
        markedArcPresent tail head ktail khead j z y∧H₀ z u)).card:ℝ)) →
    (∀ a:E⊕K,Sum.elim tail ktail a∉X→Sum.elim head khead a∉X→
      ¬PermutationClose π b (Sum.elim tail ktail a) (Sum.elim head khead a)) →
    (∀ a:E⊕K,Sum.elim tail ktail a∉X→Sum.elim head khead a∉X→
      βfree*Fintype.card (V⊕U)≤((Z.filter (fun u=>H₀ (Sum.elim tail ktail a) u∧
      (if markedArcType a then Hₖ (Sum.elim head khead a) u else H₀ (Sum.elim head khead a) u))).card:ℝ)) →
    let a:=fun r j=>((markedBalanceTermSet tail head ktail khead H₀ Hₖ r j).card:ℝ)
    let c:=fun r j=>(((markedBalanceTermSet tail head ktail khead H₀ Hₖ r j).filter (fun e=>
      (if markedActiveAuxTail tail ktail H₀ Hₖ e=r then markedActiveAuxHead head khead H₀ Hₖ e
        else markedActiveAuxTail tail ktail H₀ Hₖ e)∈ordinaryInnerVertices X Z)).card:ℝ);
    (∀ (v:V) (i:Fin 3),|markedSixDegreeBalance (l+4) (a (Sum.inl v)) i.castSucc|≤θ*Fintype.card V) →
    (∀ (v:V) (i:Fin 3),|markedSixDegreeBalance (l+4) (c (Sum.inl v)) i.castSucc|≤θ*Fintype.card V) →
    (∀ u,|markedSixDegreeBalance (l+4) (a (Sum.inr u)) 3|≤θ*Fintype.card V) →
    (∀ u,|markedSixDegreeBalance (l+4) (c (Sum.inr u)) 3|≤θ*Fintype.card V) →
    ∀ (hτ:0≤τ) (hτ1:τ≤1),
    1-4/(Fintype.card (V⊕U):ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin τ hτ hτ1)).probability
      (fun σ=>
        let PE:=fun e:E=>¬markedBoundaryRimAllowed π X σ false (tail e) (head e)
        let PK:=fun e:K=>¬markedBoundaryRimAllowed π X σ true (ktail e) (khead e)
        let t':=fun e:{e//PE e}=>tail e.val
        let h':=fun e:{e//PE e}=>head e.val
        let kt':=fun e:{e//PK e}=>ktail e.val
        let kh':=fun e:{e//PK e}=>khead e.val
        let H₀':=fun x u=>H₀ x u∧¬markedBoundarySpokeAllowed X Z σ x u
        let Hₖ':=fun x u=>Hₖ x u∧¬markedBoundarySpokeAllowed X Z σ x u;
        ∃ Mr:Finset (MarkedWheel t' h' kt' kh' (l+4) π b H₀' Hₖ'),
        let M₀:=Mr.image (markedWheelToLarger PE PK
          (fun (x:V) (u:U) (h:H₀' x u)=>h.1) (fun (x:V) (u:U) (h:Hₖ' x u)=>h.1))
        let G:=ordinaryBoundaryGraph
          (physicalEdgeGraph (Finset.univ.image (markedPhysicalEdge tail head ktail khead π)))
          (fun x u=>H₀ x u∨Hₖ x u) X Z
        let C:=ordinaryPhysicalGraph (markedPackingRimGraph M₀) (markedPackingSpokes M₀);
          (∀ W∈M₀,∀ Z∈M₀,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z)) ∧
          (∀ x:V⊕U,((markedIncidentEdges t' h' kt' kh' π H₀' Hₖ' false x \
            Mr.biUnion markedActiveResources).card:ℝ)≤τ^9*Fintype.card V) ∧
          (∀ x:V⊕U,((markedPhysicalIncidentEdges t' h' kt' kh' π H₀' Hₖ' x \
            Mr.biUnion markedWheelPhysicalResources).card:ℝ)≤τ^9*Fintype.card V) ∧
          (∀ e∈M₀.biUnion markedWheelPhysicalResources,¬markedInnerResource X Z e) ∧
          Disjoint C (retainedGraph G σ) ∧
          (∀ x,(((G\retainedGraph G σ)\C).degree x:ℝ)≤τ^9*Fintype.card V) ∧
        ∃ M₁:Finset (MarkedWheel tail head ktail khead (l+4) π b H₀ Hₖ),
          (∀ W∈M₁,∀ T∈M₁,W≠T→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources T)) ∧
          Disjoint (M₁.biUnion markedWheelPhysicalResources) (M₀.biUnion markedWheelPhysicalResources) ∧
          (∀ a:E⊕K,Sum.elim tail ktail a∉X→Sum.elim head khead a∉X→
            Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈
              M₀.biUnion markedWheelPhysicalResources∪M₁.biUnion markedWheelPhysicalResources) ∧
          (∀ x u,x∉X→u∉Z→(H₀ x u∨Hₖ x u)→Sum.inr (x,u)∈
              M₀.biUnion markedWheelPhysicalResources∪M₁.biUnion markedWheelPhysicalResources) ∧
          (∀ z,((ordinaryPhysicalGraph (markedPackingRimGraph M₁) (markedPackingSpokes M₁)).degree z:ℝ)≤τ^3*Fintype.card V) ∧
          (∀ z,((ordinaryPhysicalGraph (markedPackingRimGraph M₁) (markedPackingSpokes M₁)).degree z:ℝ)≤ν*τ^3*Fintype.card V)) := by
  obtain ⟨c₀,hc₀⟩:=marked_sampled_complement_approximation α p₀ hα hαmax hp₀ hp₀max
  refine ⟨c₀,?_⟩
  intro l hl hlc β L bminus bplus ω h δ hβ hL hbm hbp hω hh hδ hδsmall
  obtain ⟨ε,η₀,δ₀,ξ,τA,hε,hη₀,hδ₀,hξ,hτA,hτAmax,hA⟩:=hc₀ (l+3) (by omega)
    β L bminus bplus ω h δ hβ hL hbm hbp hω hh hδ hδsmall
  refine ⟨ε,η₀,δ₀,ξ,hε,hη₀,hδ₀,hξ,?_⟩
  intro βfree ν hβfree hν q
  obtain ⟨τC,hτC,hC⟩:=marked_sampled_outside_completion l hl βfree ν hβfree hν q
  refine ⟨min τA τC,by positivity,
    (min_le_left _ _).trans hτAmax,?_⟩
  intro τ hτpos hτsmall
  have hτ1:τ≤1:=le_trans (hτsmall.trans ((min_le_left _ _).trans hτAmax)) (by norm_num)
  obtain ⟨θ,hθ,hAp⟩:=hA τ hτpos (hτsmall.trans (min_le_left _ _))
  refine ⟨θ,hθ,?_⟩
  intro b hb
  obtain ⟨NA,hNA⟩:=hAp b q
  obtain ⟨NC,hNC⟩:=hC τ hτpos hτ1 (hτsmall.trans (min_le_right _ _)) b hb
  refine ⟨max NA NC,?_⟩
  intro V E K U _ _ _ _ _ _ tail head ktail khead π hphys p D hp hpmax hn hDlo hDhi
    hdo hdi hdko hdki htwo hcut H₀ Hₖ hdisj hhub hωn huV ps qs δsp Dexc hdata hsmall i hipos
    hcommon hpaths ψ hRerr hSerr hψ hcut0 hcutK hcutH0 hcutHK X Z hsize hX hstep hjoin hsep hhubs
    a c ha hc hau hcu hτ hτ1'
  have hAE:=hNA V E K U tail head ktail khead π hphys p D hp hpmax (by omega) hDlo hDhi
    hdo hdi (by convert hdko using 1 <;> push_cast <;> ring) (by convert hdki using 1 <;> push_cast <;> ring) htwo hcut H₀ Hₖ hdisj hhub hωn huV ps qs δsp Dexc hdata hsmall i hipos
    hcommon hpaths ψ hRerr hSerr hψ hcut0 hcutK hcutH0 hcutHK X Z hsize ha hc hau hcu hτ hτ1'
  have hCE:=hNC V U E K (by omega) tail head ktail khead H₀ Hₖ π X Z hphys hX hstep hjoin hsep hhubs
  have hboth:=finiteLaw_two_events_lower _ _ _ _ _ hAE hCE
  apply le_trans (b:=1-2/(Fintype.card (V⊕U):ℝ)^q-2/(Fintype.card (V⊕U):ℝ)^q)
    (by ring_nf;exact le_rfl)
  apply hboth.trans
  apply finiteLaw_probability_mono
  intro σ hσ PE PK t' h' kt' kh' H₀' Hₖ'
  obtain ⟨Mr,hMr,haux,hphysical⟩:=hσ.1
  obtain ⟨M₁,hM₁,hdisjoint,houtsideR,houtsideS,hD,hDν⟩:=hσ.2 Mr (by convert haux using 1 <;> congr!)
  let lift:=markedWheelToLarger (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
    (m:=l+4) (π:=π) (b:=b) PE PK
    (fun (x:V) (u:U) (h:H₀' x u)=>h.1) (fun (x:V) (u:U) (h:Hₖ' x u)=>h.1)
  have hcover:(Mr.image lift).biUnion markedWheelPhysicalResources=Mr.biUnion markedWheelPhysicalResources:=
    markedWheelToLarger_cover PE PK _ _ Mr
  have hbnd:=marked_complement_boundary_remainder tail head ktail khead π H₀ Hₖ (l+4) b X Z hX σ Mr
  have hg:=markedPackingResourceEquality_graphs (Mr.image lift) Mr hcover
  have hCG:ordinaryPhysicalGraph (markedPackingRimGraph (Mr.image lift)) (markedPackingSpokes (Mr.image lift))=
      ordinaryPhysicalGraph (markedPackingRimGraph Mr) (markedPackingSpokes Mr):=by
    ext x y
    cases x <;> cases y <;> simp only [ordinaryPhysicalGraph,hg.1,hg.2]
  refine ⟨Mr,?_,?_,?_,?_,?_,?_,M₁,hM₁,?_,?_,?_,hD,hDν⟩
  · exact markedWheelToLarger_matching PE PK _ _ Mr hMr
  · convert haux using 1 <;> congr!
  · convert hphysical using 1 <;> congr!
  · change ∀ e∈(Mr.image lift).biUnion markedWheelPhysicalResources,¬markedInnerResource X Z e
    rw [hcover]
    exact marked_complement_packing_avoids_inner (l+4) b X Z hX σ Mr
  · change Disjoint (ordinaryPhysicalGraph (markedPackingRimGraph (Mr.image lift)) (markedPackingSpokes (Mr.image lift))) _
    rw [hCG]
    exact hbnd.1
  · intro x
    change (((_\_)\ordinaryPhysicalGraph (markedPackingRimGraph (Mr.image lift)) (markedPackingSpokes (Mr.image lift))).degree x:ℝ)≤_
    simp only [←SimpleGraph.ncard_neighborSet,hCG]
    have hn:=hbnd.2 x
    have hn':(((ordinaryBoundaryGraph
        (physicalEdgeGraph (Finset.univ.image (markedPhysicalEdge tail head ktail khead π)))
        (fun x u=>H₀ x u∨Hₖ x u) X Z\retainedGraph (ordinaryBoundaryGraph
        (physicalEdgeGraph (Finset.univ.image (markedPhysicalEdge tail head ktail khead π)))
        (fun x u=>H₀ x u∨Hₖ x u) X Z) σ)\
        ordinaryPhysicalGraph (markedPackingRimGraph Mr) (markedPackingSpokes Mr)).degree x:ℝ)≤
      ((markedPhysicalIncidentEdges t' h' kt' kh' π H₀' Hₖ' x\Mr.biUnion markedWheelPhysicalResources).card:ℝ):=by
      exact_mod_cast hn
    simpa only [←SimpleGraph.ncard_neighborSet] using hn'.trans (by convert hphysical x using 1 <;> congr!)
  · change Disjoint _ ((Mr.image lift).biUnion markedWheelPhysicalResources)
    rw [hcover]
    exact hdisjoint
  · intro a ha hb
    change _∈(Mr.image lift).biUnion markedWheelPhysicalResources∪_
    rw [hcover]
    exact houtsideR a ha hb
  · intro x u hx hu hp
    change _∈(Mr.image lift).biUnion markedWheelPhysicalResources∪_
    rw [hcover]
    exact houtsideS x u hx hu hp
end Oberwolfach
