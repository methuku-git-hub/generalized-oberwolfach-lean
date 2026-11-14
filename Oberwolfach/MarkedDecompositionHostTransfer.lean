module

public import Oberwolfach.MarkedWheelRestriction
public import Oberwolfach.ResourceTransformers

@[expose] public section

/-! Transfer a marked wheel decomposition between different typed hosts.
Only the actual decomposed resources require compatible arc directions
and spoke types. No common physically injective superhost is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K E' K':Type} [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {tail' head':E'→V} {ktail' khead':K'→V}
  {m b:ℕ} {π:Equiv.Perm V} {H₀ HK H₀' HK':V→U→Prop}

theorem marked_wheel_transfer_on_resources
    (W:MarkedWheel tail head ktail khead m π b H₀ HK)
    (hE:∀ e:E,Sum.inl ({tail e,head e}:Finset V)∈markedWheelPhysicalResources W→
      ∃ e':E',tail' e'=tail e∧head' e'=head e)
    (hK:∀ e:K,Sum.inl ({ktail e,π (khead e)}:Finset V)∈markedWheelPhysicalResources W→
      ∃ e':K',ktail' e'=ktail e∧khead' e'=khead e)
    (h₀:∀ v u,Sum.inr (v,u)∈markedWheelPhysicalResources W→H₀ v u→H₀' v u)
    (hk:∀ v u,Sum.inr (v,u)∈markedWheelPhysicalResources W→HK v u→HK' v u):
    ∃ W':MarkedWheel tail' head' ktail' khead' m π b H₀' HK',
      W'.1.val=W.1.val∧W'.2.val=W.2.val∧markedWheelPhysicalResources W'=markedWheelPhysicalResources W:=by
  have hc:IsMarkedCycleTuple tail' head' ktail' khead' m π b W.1.val:=by
    refine ⟨W.1.property.1,?_,?_⟩
    · intro j
      obtain ⟨e,ht,hh⟩:=W.1.property.2.1 j
      have he:Sum.inl ({tail e,head e}:Finset V)∈markedWheelPhysicalResources W:=by
        apply (markedWheelPhysicalResources_rim W _).mpr
        refine Finset.mem_image.mpr ⟨j.castSucc,Finset.mem_univ _,?_⟩
        rw [Function.comp_apply,markedCyclePhysicalEdge_at]
        simp only [Fin.castSucc_ne_last,ite_false,finRotate_castSucc_eq_succ,ht,hh]
      obtain ⟨e',ht',hh'⟩:=hE e he
      exact ⟨e',ht'.trans ht,hh'.trans hh⟩
    · obtain ⟨e,ht,hh⟩:=W.1.property.2.2
      have he:Sum.inl ({ktail e,π (khead e)}:Finset V)∈markedWheelPhysicalResources W:=by
        apply (markedWheelPhysicalResources_rim W _).mpr
        refine Finset.mem_image.mpr ⟨Fin.last m,Finset.mem_univ _,?_⟩
        rw [Function.comp_apply,markedCyclePhysicalEdge_at]
        simp only [ite_true,ht,hh]
      obtain ⟨e',ht',hh'⟩:=hK e he
      exact ⟨e',ht'.trans ht,hh'.trans hh⟩
  have hs (i:Fin (m+1)):Sum.inr (W.1.val i,W.2.val)∈markedWheelPhysicalResources W:=by
    exact (markedWheelPhysicalResources_spoke W _ _).mpr
      ⟨rfl,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  let W':MarkedWheel tail' head' ktail' khead' m π b H₀' HK':=
    ⟨⟨W.1.val,hc⟩,⟨W.2.val,hk _ _ (hs 0) W.2.property.1,
      fun j=>h₀ _ _ (hs j.succ) (W.2.property.2 j)⟩⟩
  refine ⟨W',rfl,rfl,?_⟩
  have hr:markedCyclePhysicalEdges tail' head' ktail' khead' m π b W'.1=
      markedCyclePhysicalEdges tail head ktail khead m π b W.1:=by
    apply Finset.image_congr
    intro i _
    simp only [Function.comp_apply,markedCyclePhysicalEdge_at,W']
  unfold markedWheelPhysicalResources
  rw [hr]

theorem marked_decomposition_transfer_on_resources
    (S:Finset (Finset V⊕(V×U)))
    (hE:∀ e:E,Sum.inl ({tail e,head e}:Finset V)∈S→∃ e':E',tail' e'=tail e∧head' e'=head e)
    (hK:∀ e:K,Sum.inl ({ktail e,π (khead e)}:Finset V)∈S→∃ e':K',ktail' e'=ktail e∧khead' e'=khead e)
    (h₀:∀ v u,Sum.inr (v,u)∈S→H₀ v u→H₀' v u)
    (hk:∀ v u,Sum.inr (v,u)∈S→HK v u→HK' v u)
    (hS:HasResourceDecomposition
      (fun W:MarkedWheel tail head ktail khead m π b H₀ HK=>markedWheelPhysicalResources W) S):
    HasResourceDecomposition
      (fun W:MarkedWheel tail' head' ktail' khead' m π b H₀' HK'=>markedWheelPhysicalResources W) S:=by
  obtain ⟨M,hM,hcover⟩:=hS
  have hW (W:M):markedWheelPhysicalResources W.val⊆S:=by
    rw [←hcover]
    exact resource_subset_union _ M W.val W.property
  have hex (W:M):∃ W':MarkedWheel tail' head' ktail' khead' m π b H₀' HK',
      markedWheelPhysicalResources W'=markedWheelPhysicalResources W.val:=by
    obtain ⟨W',_,_,he⟩:=marked_wheel_transfer_on_resources W.val
      (fun e he=>hE e (hW W he)) (fun e he=>hK e (hW W he))
      (fun v u he hh=>h₀ v u (hW W he) hh) (fun v u he hh=>hk v u (hW W he) hh)
    exact ⟨W',he⟩
  choose f hf using hex
  refine ⟨Finset.univ.image f,?_,?_⟩
  · intro W hW Z hZ hne
    obtain ⟨W,_,rfl⟩:=Finset.mem_image.mp hW
    obtain ⟨Z,_,rfl⟩:=Finset.mem_image.mp hZ
    simpa only [hf] using hM W.val W.property Z.val Z.property (fun he=>hne (congrArg f (Subtype.ext he)))
  · rw [←hcover]
    ext e
    simp only [Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨W,⟨Z,rfl⟩,he⟩
      exact ⟨Z.val,Z.property,by rwa [hf] at he⟩
    · rintro ⟨W,hW,he⟩
      exact ⟨f ⟨W,hW⟩,⟨⟨W,hW⟩,rfl⟩,by rwa [hf]⟩

theorem marked_absorber_transfer_on_resources
    (C L:Finset (Finset V⊕(V×U)))
    (hE:∀ e:E,Sum.inl ({tail e,head e}:Finset V)∈C∪L→∃ e':E',tail' e'=tail e∧head' e'=head e)
    (hK:∀ e:K,Sum.inl ({ktail e,π (khead e)}:Finset V)∈C∪L→∃ e':K',ktail' e'=ktail e∧khead' e'=khead e)
    (h₀:∀ v u,Sum.inr (v,u)∈C∪L→H₀ v u→H₀' v u)
    (hk:∀ v u,Sum.inr (v,u)∈C∪L→HK v u→HK' v u)
    (habs:IsResourceAbsorber
      (fun W:MarkedWheel tail head ktail khead m π b H₀ HK=>markedWheelPhysicalResources W) L C):
    IsResourceAbsorber
      (fun W:MarkedWheel tail' head' ktail' khead' m π b H₀' HK'=>markedWheelPhysicalResources W) L C:=by
  refine ⟨habs.1,?_,?_⟩
  · exact marked_decomposition_transfer_on_resources C
      (fun e he=>hE e (Finset.mem_union_left _ he)) (fun e he=>hK e (Finset.mem_union_left _ he))
      (fun v u he hh=>h₀ v u (Finset.mem_union_left _ he) hh)
      (fun v u he hh=>hk v u (Finset.mem_union_left _ he) hh) habs.2.1
  · exact marked_decomposition_transfer_on_resources (C∪L) hE hK h₀ hk habs.2.2

end Oberwolfach
