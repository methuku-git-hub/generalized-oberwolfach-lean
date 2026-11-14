module

public import Oberwolfach.PrescribedSubtypeGlue

@[expose] public section
/-! When factor edges are partitioned between the earlier part and a
separately typed remainder, gluing their vertex maps preserves their exact
physical edge images. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X Y V:Type} [Fintype X] [DecidableEq X] [DecidableEq Y] [DecidableEq V]

theorem prescribed_glued_physical_edge_images (embed:X↪Y) (A:Finset Y)
    (Eold:Finset (Sym2 Y)) (Erem:Finset (Sym2 X)) (ψ h:Y→V) (Φ:X→V)
    (hold:∀x∈A,h x=ψ x) (hrem:∀x,h (embed x)=Φ x)
    (hEold:∀e∈Eold,∀v∈e.toFinset,v∈A):
    (Eold∪Erem.image (Sym2.map embed)).image (Sym2.map h)=
      Eold.image (Sym2.map ψ)∪Erem.image (Sym2.map Φ) := by
  rw [Finset.image_union,Finset.image_image]
  congr 1
  · apply Finset.image_congr
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hx:x∈A:=hEold _ he x (by simp [Sym2.toFinset_mk_eq])
      have hy:y∈A:=hEold _ he y (by simp [Sym2.toFinset_mk_eq])
      change s(h x,h y)=s(ψ x,ψ y)
      rw [hold x hx,hold y hy]
  · apply Finset.image_congr
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      change s(h (embed x),h (embed y))=s(Φ x,Φ y)
      rw [hrem x,hrem y]
end Oberwolfach
