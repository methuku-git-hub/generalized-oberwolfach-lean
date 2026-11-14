module

public import Oberwolfach.MarkedPaddedArcSeparation

@[expose] public section

/-! Canonical same-type positions for the private wheels in the expansion.
The rim tail is always ordinary. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def markedExpansionRimPosition (m:ℕ) (hm:2≤m) (j:Bool):Fin (m+1):=
  if j then Fin.last m else ⟨1,by omega⟩
def markedExpansionSpokePosition (m:ℕ) (hm:2≤m) (j:Bool):Fin (m+1):=
  if j then 0 else ⟨1,by omega⟩

theorem markedExpansionRimPosition_type (m:ℕ) (hm:2≤m) (j:Bool):
    decide (markedExpansionRimPosition m hm j=Fin.last m)=j:=by
  cases j <;> simp [markedExpansionRimPosition,Fin.ext_iff] <;> omega

theorem markedExpansionRimPosition_ne_zero (m:ℕ) (hm:2≤m) (j:Bool):
    markedExpansionRimPosition m hm j≠0:=by
  cases j <;> simp [markedExpansionRimPosition,Fin.ext_iff] <;> omega

theorem markedExpansionSpokePosition_type (m:ℕ) (hm:2≤m) (j:Bool):
    decide (markedExpansionSpokePosition m hm j=0)=j:=by
  cases j <;> simp [markedExpansionSpokePosition,Fin.ext_iff]

end Oberwolfach
