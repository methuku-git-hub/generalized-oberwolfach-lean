module

public import Oberwolfach.MarkedActiveTypedPhysicalInjection
public import Oberwolfach.ResourceRestriction

@[expose] public section
/-! Restrict the original candidate identifiers to the retained typed
resources, then map their resources injectively to physical edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color C:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [Fintype C] [LinearOrder V] [DecidableEq U] [DecidableEq C]

abbrev MarkedRetainedResource (P:SimpleGraph V) (π:Equiv.Perm V) (b d:ℕ)
    (ρ:Sym2 V→Option (Bool×Bool))
    (σ:RawIntervalFamilyOutcome V U Γ Color) (g₀:Γ) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (g:Γ) (j:Color) :=
  {z:((V×V)⊕(V×V))⊕(Bool×V×U) //
    activeTypedResource P π b ρ (retainedRawMarkedSpokes π d σ g₀ t J g j)
      ((markedResourceTypeEquiv (V:=V) (U:=U)) z)}

def markedRetainedResourcePhysicalEmbedding
    (P:SimpleGraph V) (π:Equiv.Perm V) (b d:ℕ)
    (ρ:Sym2 V→Option (Bool×Bool))
    (σ:RawIntervalFamilyOutcome V U Γ Color) (g₀:Γ) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (g:Γ) (j:Color) :
    MarkedRetainedResource P π b d ρ σ g₀ t J g j ↪ Sym2 V⊕(V×U) where
  toFun z:=typedResourcePhysical π ((markedResourceTypeEquiv (V:=V) (U:=U)) z.val)
  inj' x y h:=by
    apply Subtype.ext
    apply (markedResourceTypeEquiv (V:=V) (U:=U)).injective
    let xx : {z // activeTypedResource P π b ρ
        (retainedRawMarkedSpokes π d σ g₀ t J g j) z} :=
      ⟨(markedResourceTypeEquiv (V:=V) (U:=U)) x.val,x.property⟩
    let yy : {z // activeTypedResource P π b ρ
        (retainedRawMarkedSpokes π d σ g₀ t J g j) z} :=
      ⟨(markedResourceTypeEquiv (V:=V) (U:=U)) y.val,y.property⟩
    have h' : xx=yy := retained_marked_active_typed_physical_injective P π b d ρ σ g₀ t J g j h
    exact congrArg Subtype.val h' 

theorem marked_retained_candidate_physical_disjoint
    (P:SimpleGraph V) (π:Equiv.Perm V) (b d:ℕ)
    (ρ:Sym2 V→Option (Bool×Bool))
    (σ:RawIntervalFamilyOutcome V U Γ Color) (g₀:Γ) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (g:Γ) (j:Color)
    (R:C→Finset (((V×V)⊕(V×V))⊕(Bool×V×U)))
    (a b':RestrictedResource R (Function.Embedding.subtype
      (fun z=>activeTypedResource P π b ρ (retainedRawMarkedSpokes π d σ g₀ t J g j)
        ((markedResourceTypeEquiv (V:=V) (U:=U)) z))))
    (h:Disjoint (restrictedResourceSet R _ a) (restrictedResourceSet R _ b')):
    Disjoint ((restrictedResourceSet R _ a).map (markedRetainedResourcePhysicalEmbedding P π b d ρ σ g₀ t J g j))
      ((restrictedResourceSet R _ b').map (markedRetainedResourcePhysicalEmbedding P π b d ρ σ g₀ t J g j)) := by
  exact (Finset.disjoint_map _).mpr h
end Oberwolfach
