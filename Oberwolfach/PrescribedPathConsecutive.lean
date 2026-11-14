module

public import Oberwolfach.ExtendingListOneSidedPath

@[expose] public section
/-! The recursive path condition supplies every directed consecutive edge. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V:Type} [Fintype V] [DecidableEq V]

theorem prescribed_path_consecutive (D:V→V→Prop) (F:SimpleGraph V) (forward:Bool):
    ∀ xs:List V,∀ x:V,DirectedPathFrom D F forward x xs→
    ∀ i:ℕ,∀ hi:i+1<(x::xs).length,
      (if forward then D ((x::xs)[i]'(by omega)) ((x::xs)[i+1]'(by omega))
       else D ((x::xs)[i+1]'(by omega)) ((x::xs)[i]'(by omega))) ∧
      ¬F.Adj ((x::xs)[i]'(by omega)) ((x::xs)[i+1]'(by omega)) := by
  intro xs
  induction xs with
  | nil =>
    intro x hpath i hi
    simp at hi
  | cons z zs ih =>
    intro x hpath i hi
    cases i with
    | zero => simpa using And.intro hpath.1 hpath.2.1
    | succ i =>
      have hi':i+1<(z::zs).length:=by simpa using hi
      have hh:=ih z hpath.2.2 i hi'
      simpa using hh
end Oberwolfach
