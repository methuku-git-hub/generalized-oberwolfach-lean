module

public import Oberwolfach.PrescribedSubtypeGlue
public import Oberwolfach.PrescribedSelectedImagesAvoid

@[expose] public section
/-! Use the selected-image identity and free-list exclusion to glue a
separately typed remainder to the already embedded part of a factor. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X Y V:Type} [Fintype X] [DecidableEq X] [DecidableEq Y] [DecidableEq V] [Nonempty V]

theorem prescribed_subtype_complete_factor_glue
    (embed:X↪Y) (A:Finset Y) (A₀ B:Finset X) (ψ:Y→V) (f g Φ:X→V) (L C Z:Finset V)
    (hA₀:∀x,x∈A₀↔embed x∈A) (hA₀B:A₀⊆B)
    (hψ:Set.InjOn ψ (↑A:Set Y)) (hΦ:Function.Injective Φ)
    (hf:∀x∈A₀,f x=ψ (embed x)) (hg:∀x∈A₀,g x=f x) (hΦg:∀x∈B,Φ x=g x)
    (himage:B.image g=A₀.image f∪C∪Z)
    (hOldC:Disjoint (A.image ψ) C) (hOldZ:Disjoint (A.image ψ) Z)
    (hfree:∀x,x∉B→Φ x∈L) (hL:Disjoint L (A.image ψ)):
    ∃h:Y→V,Set.InjOn h (↑(A∪Finset.univ.image embed):Set Y) ∧
      (∀y∈A,h y=ψ y) ∧ (∀x,h (embed x)=Φ x) := by
  have hΦB:Set.InjOn Φ (↑B:Set X):=fun x _ y _ h=>hΦ h
  have hselected:∀x∈B\A₀,Φ x∉A.image ψ:=
    prescribed_selected_images_avoid_old A₀ B f g Φ (A.image ψ) C Z hA₀B hΦB hg hΦg himage hOldC hOldZ
  apply prescribed_subtype_embeddings_glue embed A ψ Φ hψ hΦ ?_ ?_
  · intro x hx
    have hx₀:x∈A₀:=(hA₀ x).mpr hx
    calc
      Φ x=g x:=hΦg x (hA₀B hx₀)
      _=f x:=hg x hx₀
      _=ψ (embed x):=hf x hx₀
  · intro x hx
    have hx₀:x∉A₀:=by intro h;exact hx ((hA₀ x).mp h)
    by_cases hxB:x∈B
    · exact hselected x (Finset.mem_sdiff.mpr ⟨hxB,hx₀⟩)
    · exact (Finset.disjoint_left.mp hL) (hfree x hxB)
end Oberwolfach
