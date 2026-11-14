module

public import Oberwolfach.PrescribedDependentSourceModel
public import Oberwolfach.PrescribedFamilyState

@[expose] public section
/-! Extend separately typed prescribed maps to the common dependent-sum
source universe, preserving their values and injectivity on the prescribed
sets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [DecidableEq I] [DecidableEq V]
  {X:I→Type} [∀ i,Fintype (X i)] [∀ i,DecidableEq (X i)]

def prescribedLiftedSet (A:∀ i,Finset (X i)) (i:I):Finset (Σ i,X i):=
  (A i).image (Sigma.mk i)

def prescribedLiftedMap (v₀:V) (ψ:∀ i,X i→V) (i:I) (z:Σ i,X i):V:=
  if h:z.1=i then ψ i (h ▸ z.2) else v₀

@[simp] theorem prescribed_lifted_map_value (v₀:V) (ψ:∀ i,X i→V) (i:I) (x:X i):
    prescribedLiftedMap v₀ ψ i (Sigma.mk i x)=ψ i x := by
  simp [prescribedLiftedMap]

theorem prescribed_lifted_set_membership (A:∀ i,Finset (X i)) (i:I) (x:X i):
    Sigma.mk i x∈prescribedLiftedSet A i ↔ x∈A i := by
  simp only [prescribedLiftedSet,Finset.mem_image]
  constructor
  · rintro ⟨y,hy,he⟩
    have h:y=x:=sigma_mk_injective he
    simpa [h] using hy
  · intro hx;exact ⟨x,hx,rfl⟩

theorem prescribed_lifted_maps_injective (v₀:V) (A:∀ i,Finset (X i)) (ψ:∀ i,X i→V)
    (hinj:∀ i,Set.InjOn (ψ i) (↑(A i):Set (X i))):
    FamilyPartialInjections (prescribedLiftedSet A) (prescribedLiftedMap v₀ ψ) := by
  intro i u hu v hv h
  obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hu
  obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hv
  simp only [prescribed_lifted_map_value] at h
  have hxy:=hinj i hx hy h
  subst y
  rfl

theorem prescribed_lifted_occurrence_bound (v₀:V) (A:∀ i,Finset (X i)) (ψ:∀ i,X i→V) (v:V):
    (Finset.univ.filter (fun i=>∃ z,z∈prescribedLiftedSet A i ∧ prescribedLiftedMap v₀ ψ i z=v)) =
      (Finset.univ.filter (fun i=>∃ x,x∈A i ∧ ψ i x=v)) := by
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨z,hz,he⟩
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hz
    exact ⟨x,hx,by simpa using he⟩
  · rintro ⟨x,hx,he⟩
    exact ⟨Sigma.mk i x,(prescribed_lifted_set_membership A i x).mpr hx,by simpa using he⟩
end Oberwolfach
