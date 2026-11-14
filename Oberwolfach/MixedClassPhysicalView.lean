module

public import Oberwolfach.MarkedGlobalOrdinaryView

@[expose] public section
/-! Ordinary and marked classes can take different views of the same physical
sample without assuming the classes' physical graphs are independent. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def mixedClassState (marked:Bool) (A B:Type):Type:=if marked then A else B
instance mixedClassStateFintype (marked:Bool) (A B:Type) [Fintype A] [Fintype B]:
    Fintype (mixedClassState marked A B):=by cases marked <;> dsimp [mixedClassState] <;> infer_instance

def mixedClassView {Ω A B:Type} (marked:Bool) (f:Ω→A) (g:Ω→B):Ω→mixedClassState marked A B:=by
  cases marked
  · exact g
  · exact f

def mixedClassLaw {A B:Type} [Fintype A] [Fintype B]
    (marked:Bool) (μ:FiniteLaw A) (ν:FiniteLaw B):FiniteLaw (mixedClassState marked A B):=by
  cases marked
  · exact ν
  · exact μ

theorem mixed_class_physical_view {Ω A B:Type} [Fintype Ω] [Fintype A] [Fintype B]
    (global:FiniteLaw Ω) (marked:Bool) (f:Ω→A) (g:Ω→B) (μ:FiniteLaw A) (ν:FiniteLaw B)
    (hf:global.map f=μ) (hg:global.map g=ν):
    global.map (mixedClassView marked f g)=mixedClassLaw marked μ ν:=by
  cases marked with
  | false => exact hg
  | true => exact hf
end Oberwolfach
