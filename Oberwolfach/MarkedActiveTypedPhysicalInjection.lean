module

public import Oberwolfach.MarkedSampleArcs
public import Oberwolfach.RetainedMarkedSpokeGeometry

@[expose] public section
/-! On the actual retained typed resources, the physical map is injective:
physical rim edges have one sampled orientation and type, and physical
spokes cannot be retained in both types. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [LinearOrder V] [DecidableEq U]

def activeTypedResource (P:SimpleGraph V) (π:Equiv.Perm V) (b:ℕ)
    (σ:Sym2 V→Option (Bool×Bool)) (H:Bool→V→U→Prop):
    (Bool×V×V) ⊕ (Bool×V×U) → Prop
  | .inl (a,x,y) => markedPhysicalRim P π b σ a x y=1
  | .inr (a,v,u) => H a v u

def typedResourcePhysical (π:Equiv.Perm V):
    (Bool×V×V) ⊕ (Bool×V×U) → Sym2 V ⊕ (V×U)
  | .inl (a,x,y) => .inl s(x,if a then π y else y)
  | .inr (_,v,u) => .inr (v,u)

theorem active_typed_resource_physical_injective
    (P:SimpleGraph V) (π:Equiv.Perm V) (b:ℕ)
    (σ:Sym2 V→Option (Bool×Bool)) (H:Bool→V→U→Prop)
    (hdisjoint:∀v u,¬(H false v u ∧ H true v u)):
    Function.Injective (fun x:{z // activeTypedResource P π b σ H z}=>
      typedResourcePhysical π x.val) := by
  intro x y he
  apply Subtype.ext
  obtain ⟨x,hx⟩:=x
  obtain ⟨y,hy⟩:=y
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      rcases x with ⟨a,x₁,x₂⟩
      rcases y with ⟨a',y₁,y₂⟩
      have he' : s(x₁,if a then π x₂ else x₂)=s(y₁,if a' then π y₂ else y₂) := by
        simpa [typedResourcePhysical] using he
      have hh:=markedPhysicalRim_physical_unique P π b σ a a' x₁ x₂ y₁ y₂ hx hy he'
      rcases hh with ⟨rfl,rfl,rfl⟩
      rfl
    | inr y => simp [typedResourcePhysical] at he
  | inr x =>
    cases y with
    | inl y => simp [typedResourcePhysical] at he
    | inr y =>
      rcases x with ⟨a,x₁,x₂⟩
      rcases y with ⟨a',y₁,y₂⟩
      have he' : (x₁,x₂)=(y₁,y₂) := by simpa [typedResourcePhysical] using he
      cases he'
      change H a x₁ x₂ at hx
      change H a' x₁ x₂ at hy
      have ha:a=a' := by
        cases a <;> cases a'
        · rfl
        · exact False.elim (hdisjoint x₁ x₂ ⟨hx,hy⟩)
        · exact False.elim (hdisjoint x₁ x₂ ⟨hy,hx⟩)
        · rfl
      cases ha
      rfl
/-- The spoke disjointness required above holds for the actual retained
interval sample, without further restrictions on the retained starts. -/
theorem retained_marked_active_typed_physical_injective
    {Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    (P:SimpleGraph V) (π:Equiv.Perm V) (b d:ℕ)
    (ρ:Sym2 V→Option (Bool×Bool))
    (σ:RawIntervalFamilyOutcome V U Γ Color) (g₀:Γ) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (g:Γ) (j:Color):
    Function.Injective (fun x:{z // activeTypedResource P π b ρ
      (retainedRawMarkedSpokes π d σ g₀ t J g j) z}=>typedResourcePhysical π x.val) := by
  exact active_typed_resource_physical_injective P π b ρ _
    (retainedMarkedSpokes_disjoint π d σ g₀ t J g j)
/-- The natural resource types used for marked wheels differ only in the
packaging of the two rim types. -/
def markedResourceTypeEquiv :
    ((V×V)⊕(V×V))⊕(Bool×V×U) ≃ (Bool×V×V)⊕(Bool×V×U) :=
  Equiv.sumCongr (Equiv.boolProdEquivSum (V×V)).symm (Equiv.refl _)

theorem markedResourceTypeEquiv_ordinary (x y:V) :
    (markedResourceTypeEquiv (U:=U)) (Sum.inl (Sum.inl (x,y)))=Sum.inl (false,x,y) := rfl

theorem markedResourceTypeEquiv_marked (x y:V) :
    (markedResourceTypeEquiv (U:=U)) (Sum.inl (Sum.inr (x,y)))=Sum.inl (true,x,y) := rfl

theorem markedResourceTypeEquiv_spoke (a:Bool) (v:V) (u:U) :
    markedResourceTypeEquiv (Sum.inr (a,v,u))=Sum.inr (a,v,u) := rfl
end Oberwolfach
