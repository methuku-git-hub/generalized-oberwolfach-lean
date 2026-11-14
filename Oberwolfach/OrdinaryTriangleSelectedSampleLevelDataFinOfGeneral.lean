module

public import Oberwolfach.OrdinaryTriangleSelectedSampleLevelDataGeneral

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem ordinary_triangle_selected_sample_level_fin_of_general
    (n q D mv k d:ℕ) (β ε:ℝ) (P:SimpleGraph (Fin n))
    (Q:Vortex (Fin q) P D β ε mv) (π:Equiv.Perm (Fin n))
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (α ρ₀ pstar βP ηP ηH βH cParent Bparent εTri δref href:ℝ)
    (pR pH pmin κ aLoad εR εH bInner BInner ηInner capInner βe βh:ℝ)
    (density tR tH:ℕ→ℝ) (s:Fin q→Bool→ℝ) (j:Bool)
    (raw:RawWheelOutcome (Fin n) (Fin q) Bool Bool) (coins:Sym2 (Fin n)→Bool) (i:ℕ)
    (weight:OrdinaryCycle (P.comap (markedVortexVertexEmbedding Q i)) 3→ℝ)
    (h:OrdinaryTriangleSelectedSampleLevelDataGeneral D mv k d β ε P Q π hπ
      α ρ₀ pstar βP ηP ηH βH cParent Bparent εTri δref href
      pR pH pmin κ aLoad εR εH bInner BInner ηInner capInner βe βh density tR tH s j raw coins i weight):
    OrdinaryTriangleSelectedSampleLevelData n q D mv k d β ε P Q π hπ
      α ρ₀ pstar βP ηP ηH βH cParent Bparent εTri δref href
      pR pH pmin κ aLoad εR εH bInner BInner ηInner capInner βe βh density tR tH s j raw coins i weight :=by
  unfold OrdinaryTriangleSelectedSampleLevelData
  unfold OrdinaryTriangleSelectedSampleLevelDataGeneral at h
  obtain ⟨hfamily,hfine,hrow,htwo,hrim,hevent,hcuts,hinputs,hweight⟩:=h
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · convert hfamily using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
  · convert hfine using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
  · convert hrow using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
  · convert htwo using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
  · convert hrim using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
  · convert hevent using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
  · convert hcuts using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
  · convert hinputs using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
  · convert hweight using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
end Oberwolfach
