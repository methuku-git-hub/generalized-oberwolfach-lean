module

public import Oberwolfach.PrescribedPathPhysicalEdges
public import Oberwolfach.PrescribedOneSidedPhysicalEdges

@[expose] public section
/-! Mapping source vertices carries exactly the physical edges of each path
to the physical edges of the image path. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X V:Type} [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V]

theorem prescribed_path_physical_map (g:X→V) (y:X):
    ∀ (xs:List X) (x:X),
    (prescribedPathPhysicalEdges x y xs).image (Sym2.map g)=
      prescribedPathPhysicalEdges (g x) (g y) (xs.map g) := by
  intro xs
  induction xs with
  | nil => intro x;simp [prescribedPathPhysicalEdges]
  | cons z zs ih => intro x;simp [prescribedPathPhysicalEdges,ih]

theorem prescribed_one_sided_physical_map (g:X→V):
    ∀ (xs:List X) (x:X),
    (prescribedOneSidedPhysicalEdges x xs).image (Sym2.map g)=
      prescribedOneSidedPhysicalEdges (g x) (xs.map g) := by
  intro xs
  induction xs with
  | nil => intro x;simp [prescribedOneSidedPhysicalEdges]
  | cons z zs ih => intro x;simp [prescribedOneSidedPhysicalEdges,ih]
end Oberwolfach
