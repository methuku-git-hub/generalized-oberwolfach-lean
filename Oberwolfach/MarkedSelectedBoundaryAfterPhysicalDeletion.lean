module

public import Oberwolfach.MarkedSelectedBoundaryCompletion
public import Oberwolfach.MarkedBoundaryPhysicalDeletion
public import Oberwolfach.MarkedHubFactorPhysicalRestriction
public import Oberwolfach.MarkedEndpointPhysicalRestriction
public import Oberwolfach.MarkedPackingPhysicalAvoidance
public import Oberwolfach.MarkedRootArcRestriction

@[expose] public section

/-! Complete the selected boundary in the actual host remaining after a
physical deletion. The incoming and outgoing arcs, root spokes, selected
factors and endpoint assignments all retain their original identities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T J I:Type} [Fintype V] [Fintype U] [Fintype J] [Fintype I]
    [DecidableEq V] [DecidableEq U] [DecidableEq J] [DecidableEq I]
    {tail head:E→V} {ktail khead:T→V} {H₀ HK:V→U→Prop}
    {π:Equiv.Perm V} {b l:ℕ} {c:ℝ}

theorem marked_selected_boundary_after_physical_deletion
    (X:Finset V) (Q:MarkedBoundaryExtensionCounts tail head ktail khead H₀ HK X c)
    (hl:2≤l) (hb:1≤b) (hphys:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hX:∀ x,π x∈X↔x∈X) (root:J↪V) (hrootX:∀ j,root j∉X)
    (A₀ A₁ X₀ X₁:J→Finset V) (Y₀ Y₁:J→Finset U)
    (P:∀ j,MarkedEndpointPairing (A₀ j) (A₁ j) (X₀ j) (X₁ j) (Y₀ j) (Y₁ j) H₀ HK π b)
    (hcross:∀ j k,j≠k→Disjoint (P j).graph (P k).graph)
    (incoming:∀ j,(A₀ j⊕A₁ j)↪E⊕T) (outgoing:∀ j,(X₀ j⊕X₁ j)↪E⊕T)
    (hinhead:∀ j a,Sum.elim head khead (incoming j a)=root j)
    (hintail:∀ j a,Sum.elim tail ktail (incoming j a)=taggedSubsetValue (A₀ j) (A₁ j) a)
    (houttail:∀ j a,Sum.elim tail ktail (outgoing j a)=root j)
    (houthead:∀ j a,Sum.elim head khead (outgoing j a)=taggedSubsetValue (X₀ j) (X₁ j) a)
    (hintype:∀ j a,(incoming j a).isRight=a.isRight)
    (houttype:∀ j a,(outgoing j a).isRight=a.isRight)
    (hAX:∀ j,A₀ j∪A₁ j⊆X) (hXX:∀ j,X₀ j∪X₁ j⊆X)
    (hsepA:∀ j a,a∈A₀ j∪A₁ j→¬PermutationClose π b a (root j))
    (hsepX:∀ j a,a∈X₀ j∪X₁ j→¬PermutationClose π b a (root j))
    (hY₀:∀ j u,u∈Y₀ j→H₀ (root j) u) (hY₁:∀ j u,u∈Y₁ j→HK (root j) u)
    (D K:ℕ) (hK:0<K) (hdeg:∀ w,(⨆ j,(P j).graph).degree w≤D)
    (Z:Finset U) (hYZ:∀ j,Y₀ j∪Y₁ j⊆Z)
    (hub:I↪U) (houtside:∀ j,hub j∉Z) (Y:I→Finset V) (hYX:∀ j,Y j⊆X)
    (F:∀ j,MarkedHubFactorOn tail head ktail khead (l+3) π b H₀ HK (hub j) (Y j))
    (hFcross:∀ j k,j≠k→Disjoint (F j).rim (F k).rim)
    (hFsep:∀ j v z,H₀ v (hub j)→HK z (hub j)→v≠π z)
    (δ:ℝ) (hδ:0≤δ) (hG:∀ v,((⨆ j,(F j).rim).degree v:ℝ)≤δ)
    (D₀:SimpleGraph (V⊕U)) (δ₀:ℝ) (hδ₀:0≤δ₀) (hD₀:∀ z,(D₀.degree z:ℝ)≤δ₀)
    (hPD₀:∀ j,Disjoint (P j).graph D₀) (hFD₀:∀ i,Disjoint (F i).graph D₀)
    (hrootSpokeD₀:∀ j u,u∈Y₀ j∪Y₁ j→¬D₀.Adj (Sum.inl (root j)) (Sum.inr u))
    (hfactorSpokeD₀:∀ i v,v∈Y i→¬D₀.Adj (Sum.inl v) (Sum.inr (hub i)))
    (hinD₀:∀ j a,Sum.elim
      (fun e=>¬D₀.Adj (Sum.inl (tail e)) (Sum.inl (head e)))
      (fun e=>¬D₀.Adj (Sum.inl (ktail e)) (Sum.inl (π (khead e)))) (incoming j a))
    (houtD₀:∀ j a,Sum.elim
      (fun e=>¬D₀.Adj (Sum.inl (tail e)) (Sum.inl (head e)))
      (fun e=>¬D₀.Adj (Sum.inl (ktail e)) (Sum.inl (π (khead e)))) (outgoing j a))
    (hbudget:(Fintype.card (Σ j,Y₀ j⊕Y₁ j)*(l+4):ℕ)/(K:ℝ)+D+(D*(l+4):ℕ)+
      (l+5)*(2*b+1)+2*(δ+4*(K+D:ℕ))<c-3*δ₀):
    ∃ M:Finset (MarkedWheel tail head ktail khead (l+3) π b H₀ HK),
      (∀ W∈M,∀ W'∈M,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))∧
      (∀ j a,Sum.inl (markedPhysicalEdge tail head ktail khead π (incoming j a))∈M.biUnion markedWheelPhysicalResources)∧
      (∀ j a,Sum.inl (markedPhysicalEdge tail head ktail khead π (outgoing j a))∈M.biUnion markedWheelPhysicalResources)∧
      (∀ j u,u∈Y₀ j∪Y₁ j→Sum.inr (root j,u)∈M.biUnion markedWheelPhysicalResources)∧
      (∀ j x,x∈Y j→Sum.inr (x,hub j)∈M.biUnion markedWheelPhysicalResources)∧
      (∀ v,((spanningRestriction (markedPackingRimGraph M) X).degree v:ℝ)≤δ+4*(K+D:ℕ))∧
      (∀ v∈X,(Z.filter (markedPackingSpokes M v)).card≤K+D)∧
      (∀ u∈Z,(Finset.univ.filter (fun v=>markedPackingSpokes M v u)).card≤D*(l+4))∧
      Disjoint (ordinaryPhysicalGraph (markedPackingRimGraph M) (markedPackingSpokes M)) D₀∧
      (∀ B:Finset (Finset V⊕(V×U)),
        (∀ e∈B,¬markedInnerResource X Z e)→
        (∀ j a,Sum.inl (markedPhysicalEdge tail head ktail khead π (incoming j a))∉B)→
        (∀ j a,Sum.inl (markedPhysicalEdge tail head ktail khead π (outgoing j a))∉B)→
        (∀ j u,u∈Y₀ j∪Y₁ j→Sum.inr (root j,u)∉B)→
        (∀ j x,x∈Y j→Sum.inr (x,hub j)∉B)→
        Disjoint (M.biUnion markedWheelPhysicalResources) B) :=by
  let PE:=fun e:E=>¬D₀.Adj (Sum.inl (tail e)) (Sum.inl (head e))
  let PT:=fun e:T=>¬D₀.Adj (Sum.inl (ktail e)) (Sum.inl (π (khead e)))
  let H₀':=fun v u=>H₀ v u∧¬D₀.Adj (Sum.inl v) (Sum.inr u)
  let HK':=fun v u=>HK v u∧¬D₀.Adj (Sum.inl v) (Sum.inr u)
  have hP (j:J):∃ P':MarkedEndpointPairing (A₀ j) (A₁ j) (X₀ j) (X₁ j) (Y₀ j) (Y₁ j) H₀' HK' π b,
      P'.incoming=(P j).incoming∧P'.outgoing=(P j).outgoing∧P'.graph=(P j).graph:=
    marked_endpoint_physical_restriction _ _ _ _ _ _ _ _ _ _ (P j) D₀ (hPD₀ j)
  choose P' hPi hPo hPg using hP
  have hF (i:I):∃ F':MarkedHubFactorOn (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e // PT e}=>ktail e.val) (fun e=>khead e.val) (l+3) π b H₀' HK' (hub i) (Y i),
      F'.rim=(F i).rim∧F'.graph=(F i).graph:=
    marked_hub_factor_physical_restriction (by omega) hb (hub i) (Y i) (F i) D₀ (hFD₀ i) (hfactorSpokeD₀ i)
  choose F' hFr hFg using hF
  let inc:=fun j=>restrictedSumEmbedding (incoming j) PE PT (hinD₀ j)
  let out:=fun j=>restrictedSumEmbedding (outgoing j) PE PT (houtD₀ j)
  have hPcross:∀ j k,j≠k→Disjoint (P' j).graph (P' k).graph:=by
    intro j k hne;rw [hPg,hPg];exact hcross j k hne
  have hFcross':∀ j k,j≠k→Disjoint (F' j).rim (F' k).rim:=by
    intro j k hne;rw [hFr,hFr];exact hFcross j k hne
  have hPdeg:∀ w,(⨆ j,(P' j).graph).degree w≤D:=by
    have he:(⨆ j,(P' j).graph)=⨆ j,(P j).graph:=iSup_congr hPg
    intro w;rw [he];exact hdeg w
  have hFdeg:∀ v,((⨆ j,(F' j).rim).degree v:ℝ)≤δ:=by
    have he:(⨆ j,(F' j).rim)=⨆ j,(F j).rim:=iSup_congr hFr
    intro v;rw [he];exact hG v
  have Q':=marked_boundary_counts_after_physical_deletion π X c Q D₀ δ₀ hδ₀ hD₀
  obtain ⟨M,hM,hi,ho,hroot,hcol,hr,hs,hc,havoidB⟩:=marked_selected_boundary_completion X Q' hl hb
    (markedRestrictedPhysical_injective PE PT hphys) hX root hrootX
    A₀ A₁ X₀ X₁ Y₀ Y₁ P' hPcross inc out
    (fun j a=>(restrictedSumEmbedding_elim (incoming j) PE PT (hinD₀ j) head khead a).trans (hinhead j a))
    (fun j a=>(restrictedSumEmbedding_elim (incoming j) PE PT (hinD₀ j) tail ktail a).trans (hintail j a))
    (fun j a=>(restrictedSumEmbedding_elim (outgoing j) PE PT (houtD₀ j) tail ktail a).trans (houttail j a))
    (fun j a=>(restrictedSumEmbedding_elim (outgoing j) PE PT (houtD₀ j) head khead a).trans (houthead j a))
    (fun j a=>(restrictedSumEmbedding_type (incoming j) PE PT (hinD₀ j) a).trans (hintype j a))
    (fun j a=>(restrictedSumEmbedding_type (outgoing j) PE PT (houtD₀ j) a).trans (houttype j a))
    hAX hXX hsepA hsepX
    (fun j u hu=>⟨hY₀ j u hu,hrootSpokeD₀ j u (Finset.mem_union_left _ hu)⟩)
    (fun j u hu=>⟨hY₁ j u hu,hrootSpokeD₀ j u (Finset.mem_union_right _ hu)⟩)
    D K hK hPdeg Z hYZ hub houtside Y hYX F' hFcross'
    (fun i v z hv hz=>hFsep i v z hv.1 hz.1) δ hδ hFdeg hbudget
  let lift:=fun W:MarkedWheel (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e // PT e}=>ktail e.val) (fun e=>khead e.val) (l+3) π b H₀' HK'=>
    markedWheelToLarger PE PT (fun x u (h:H₀' x u)=>h.1) (fun x u (h:HK' x u)=>h.1) W
  let N:=M.image lift
  have hcover:N.biUnion markedWheelPhysicalResources=M.biUnion markedWheelPhysicalResources:=
    markedWheelToLarger_cover PE PT _ _ M
  have hrim:markedPackingRimGraph N=markedPackingRimGraph M:=marked_packing_lift_rim PE PT _ _ M
  have hspokes:markedPackingSpokes N=markedPackingSpokes M:=marked_packing_lift_spokes PE PT _ _ M
  have hphysical (a:{e // PE e}⊕{e // PT e}):
      markedPhysicalEdge (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e:{e // PT e}=>ktail e.val) (fun e=>khead e.val) π a=
      markedPhysicalEdge tail head ktail khead π (Sum.map Subtype.val Subtype.val a):=by cases a <;> rfl
  refine ⟨N,markedWheelToLarger_matching PE PT _ _ M hM,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j a
    rw [hcover]
    have hh:=hi j a
    rw [hphysical,restrictedSumEmbedding_forget] at hh
    exact hh
  · intro j a
    rw [hcover]
    have hh:=ho j a
    rw [hphysical,restrictedSumEmbedding_forget] at hh
    exact hh
  · intro j u hu;rw [hcover];exact hroot j u hu
  · intro i v hv;rw [hcover];exact hcol i v hv
  · intro v;rw [hrim];convert hr v using 1 <;> congr!
  · intro v hv;rw [hspokes];convert hs v hv using 1 <;> congr!
  · intro u hu;rw [hspokes];convert hc u hu using 1 <;> congr!
  · rw [hrim,hspokes]
    exact marked_restricted_packing_physical_avoidance D₀ M

  · intro B hB hiB hoB hrB hhB
    rw [hcover]
    apply havoidB B hB
    · intro j a
      change Sum.inl (markedPhysicalEdge (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e:{e // PT e}=>ktail e.val) (fun e=>khead e.val) π (inc j a))∉B
      rw [hphysical,restrictedSumEmbedding_forget]
      exact hiB j a
    · intro j a
      change Sum.inl (markedPhysicalEdge (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e:{e // PT e}=>ktail e.val) (fun e=>khead e.val) π (out j a))∉B
      rw [hphysical,restrictedSumEmbedding_forget]
      exact hoB j a
    · exact hrB
    · exact hhB

end Oberwolfach
