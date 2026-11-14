module

public import Oberwolfach.AbsorberFreeRecords
public import Oberwolfach.FiniteFibreCodes

@[expose] public section

/-! Forgetting roots has bounded fibres. The internal factor stays in
the free record; the omitted root assignment and second-factor indices
are counted separately. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] {c : ℕ}

theorem labelledCycleRecord_ext {h : ℕ} {O : Type*} [Fintype O] [DecidableEq O]
    (R : C → Finset V) (S : O → Finset (Fin h ⊕ Fin c)) (X : Finset V)
    (D E : LabelledCycleRecord R S X) (hf : ∀ j,D.1.val j=E.1.val j)
    (hg : ∀ o,(D.2 o).val=(E.2 o).val) : D=E := by
  rcases D with ⟨f,d⟩
  rcases E with ⟨g,e⟩
  have he : f=g := Subtype.ext (funext hf)
  subst g
  have he' : d=e := funext (fun o => Subtype.ext (hg o))
  subst e
  rfl

theorem free_absorber_records_card (R : C → Finset V) (S : VertexAbsorberTemplate c) (J : ℕ)
    (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J) :
    Fintype.card (FreeAbsorberRecord R S) ≤ Fintype.card V^(c*c)*J^c := by
  obtain ⟨code,hcode⟩ := finite_fibre_codes R J hJ
  let enc (D : FreeAbsorberRecord R S) : (Fin (c*c) → V) × (Fin c → Fin J) :=
    (D.1,fun i => code (D.2 i).val)
  have hinj : Function.Injective enc := by
    rintro ⟨f,d⟩ ⟨g,e⟩ he
    have hf : f=g := DFunLike.coe_injective (congrArg Prod.fst he)
    subst g
    have hid : d=e := by
      funext i
      apply Subtype.ext
      apply hcode
      · exact (d i).property.trans (e i).property.symm
      · exact congrFun (congrArg Prod.snd he) i
    subst e
    rfl
  have hh := Fintype.card_le_of_injective enc hinj
  simpa only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin] using hh

theorem forget_absorber_roots_fibre_card (R : C → Finset V) (S : VertexAbsorberTemplate c)
    (X : Finset V) (J : ℕ)
    (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J) (F : FreeAbsorberRecord R S) :
    Fintype.card {D : LabelledCycleRecord R S.val X // forgetAbsorberRoots R S X D=F} ≤
      X.card^c*J^(c+1) := by
  obtain ⟨code,hcode⟩ := finite_fibre_codes R J hJ
  let A := {D : LabelledCycleRecord R S.val X // forgetAbsorberRoots R S X D=F}
  let enc (D : A) : (Fin c → X) × (Fin (c+1) → Fin J) :=
    (fun i => ⟨D.val.1.val (Sum.inr i),rootedLabelMap_root_mem X D.val.1 i⟩,
     fun i => code (D.val.2 (Sum.inr i)).val)
  have hinj : Function.Injective enc := by
    intro D E he
    have hf (j : Fin (c*c) ⊕ Fin c) : D.val.1.val j=E.val.1.val j := by
      rcases j with j | j
      · have hd := congrArg (fun F : FreeAbsorberRecord R S => F.1 j) D.property
        have he' := congrArg (fun F : FreeAbsorberRecord R S => F.1 j) E.property
        exact hd.trans he'.symm
      · exact congrArg (fun z : X => z.val) (congrFun (congrArg Prod.fst he) j)
    apply Subtype.ext
    apply labelledCycleRecord_ext R S.val X D.val E.val hf
    intro o
    rcases o with i | i
    · have hd := congrArg (fun F : FreeAbsorberRecord R S => (F.2 i).val) D.property
      have he' := congrArg (fun F : FreeAbsorberRecord R S => (F.2 i).val) E.property
      exact hd.trans he'.symm
    · apply hcode
      · rw [(D.val.2 (Sum.inr i)).property,(E.val.2 (Sum.inr i)).property]
        exact congrArg (Finset.image · (S.val (Sum.inr i))) (funext hf)
      · exact congrFun (congrArg Prod.snd he) i
  have hh := Fintype.card_le_of_injective enc hinj
  simpa only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe] using hh

end Oberwolfach
