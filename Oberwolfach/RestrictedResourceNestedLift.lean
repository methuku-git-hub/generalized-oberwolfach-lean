module

public import Oberwolfach.ResourceRestriction

@[expose] public section
/-! A matching on a surviving subdomain retains its original resource IDs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W₁ W₂ C:Type} [Fintype V] [DecidableEq V] [Fintype W₁] [DecidableEq W₁]
  [Fintype W₂] [DecidableEq W₂] [Fintype C] [DecidableEq C]

def restrictedResourceNestedLift (R:C→Finset V) (e₁:W₁↪V) (e₂:W₂↪V) (f:W₁↪W₂)
    (hf:∀w,e₂ (f w)=e₁ w):RestrictedResource R e₁↪RestrictedResource R e₂ where
  toFun c:=⟨c.val,by
    intro v hv
    obtain ⟨w,hw⟩:=c.property v hv
    exact ⟨f w,(hf w).trans hw⟩⟩
  inj' :=by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun x:RestrictedResource R e₂=>x.val) h

theorem restricted_resource_nested_lift_id (R:C→Finset V) (e₁:W₁↪V) (e₂:W₂↪V) (f:W₁↪W₂)
    (hf:∀w,e₂ (f w)=e₁ w) (c:RestrictedResource R e₁):
    (restrictedResourceNestedLift R e₁ e₂ f hf c).val=c.val :=rfl

theorem restricted_resource_nested_lift_set (R:C→Finset V) (e₁:W₁↪V) (e₂:W₂↪V) (f:W₁↪W₂)
    (hf:∀w,e₂ (f w)=e₁ w) (c:RestrictedResource R e₁):
    restrictedResourceSet R e₂ (restrictedResourceNestedLift R e₁ e₂ f hf c)=
      (restrictedResourceSet R e₁ c).map f :=by
  ext w
  simp only [restrictedResourceSet_mem,Finset.mem_map,restricted_resource_nested_lift_id]
  constructor
  · intro hw
    obtain ⟨z,hz⟩:=c.property (e₂ w) hw
    have he:f z=w:=e₂.injective ((hf z).trans hz)
    exact ⟨z,by rw [hz];exact hw,he⟩
  · rintro ⟨z,hz,rfl⟩
    rw [hf]
    exact hz

theorem restricted_resource_nested_lift_matching (R:C→Finset V) (e₁:W₁↪V) (e₂:W₂↪V) (f:W₁↪W₂)
    (hf:∀w,e₂ (f w)=e₁ w) (M:Finset (RestrictedResource R e₁))
    (hmatch:∀a∈M,∀b∈M,a≠b→Disjoint (restrictedResourceSet R e₁ a) (restrictedResourceSet R e₁ b)):
    ∀a∈M.map (restrictedResourceNestedLift R e₁ e₂ f hf),
    ∀b∈M.map (restrictedResourceNestedLift R e₁ e₂ f hf),a≠b→
      Disjoint (restrictedResourceSet R e₂ a) (restrictedResourceSet R e₂ b) :=by
  intro a ha b hb hne
  obtain ⟨a₀,ha₀,heqa⟩:=Finset.mem_map.mp ha
  obtain ⟨b₀,hb₀,heqb⟩:=Finset.mem_map.mp hb
  subst a
  subst b
  rw [restricted_resource_nested_lift_set,restricted_resource_nested_lift_set]
  apply Finset.disjoint_left.mpr
  intro v hv hw
  obtain ⟨x,hx,hxv⟩:=Finset.mem_map.mp hv
  obtain ⟨y,hy,hyv⟩:=Finset.mem_map.mp hw
  have hxy:x=y:=f.injective (hxv.trans hyv.symm)
  subst y
  exact (Finset.disjoint_left.mp (hmatch a₀ ha₀ b₀ hb₀ (fun h=>hne (congrArg (restrictedResourceNestedLift R e₁ e₂ f hf) h)))) hx hy

theorem restricted_resource_nested_lift_count (R:C→Finset V) (e₁:W₁↪V) (e₂:W₂↪V) (f:W₁↪W₂)
    (hf:∀w,e₂ (f w)=e₁ w) (M:Finset (RestrictedResource R e₁)) (p:C→Prop) [DecidablePred p]:
    ((M.map (restrictedResourceNestedLift R e₁ e₂ f hf)).filter (fun c=>p c.val)).card =
      (M.filter (fun c=>p c.val)).card :=by
  have hs:(M.map (restrictedResourceNestedLift R e₁ e₂ f hf)).filter (fun c=>p c.val)=
      (M.filter (fun c=>p c.val)).map (restrictedResourceNestedLift R e₁ e₂ f hf):=by
    ext c
    simp only [Finset.mem_filter,Finset.mem_map]
    constructor
    · rintro ⟨⟨a,ha,rfl⟩,hp⟩
      exact ⟨a,⟨ha,hp⟩,rfl⟩
    · rintro ⟨a,⟨ha,hp⟩,rfl⟩
      exact ⟨⟨a,ha,rfl⟩,hp⟩
  rw [hs,Finset.card_map]
end Oberwolfach
