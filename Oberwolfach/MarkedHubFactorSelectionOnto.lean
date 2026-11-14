module

public import Oberwolfach.MarkedHubFactorRootBijection

@[expose] public section
/-! Any root-correct selection into a disjoint hub factor covers every
wheel when its marked roots are exactly the prescribed set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_hub_factor_selection_onto
    {V U E K:Type*} [Fintype V] [DecidableEq V]
    (tail head:E→V) (ktail khead:K→V) (m b:ℕ) (π:Equiv.Perm V)
    (H₀ Hₖ:V→U→Prop) (u:U)
    (M:Finset (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u))
    (hM:∀C∈M,∀D∈M,C≠D→Disjoint (hubMarkedCycleVertices u C) (hubMarkedCycleVertices u D))
    (Y:Finset V) (hmarked:∀x,Hₖ x u↔x∈Y)
    (select:{x // x∈Y}↪HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u)
    (hselected:∀x,select x∈M ∧ (select x).val 0=x.val):
    ∀C∈M,∃x:{x // x∈Y},select x=C := by
  intro C hCM
  have hx:C.val 0∈Y:=(hmarked (C.val 0)).1 C.property.2.1
  let x:{x // x∈Y}:=⟨C.val 0,hx⟩
  refine ⟨x,?_⟩
  by_contra hne
  have hdis:=hM (select x) (hselected x).1 C hCM hne
  have hroot:(select x).val 0=C.val 0:=by simpa [x] using (hselected x).2
  have ha:(select x).val 0∈hubMarkedCycleVertices u (select x):=Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩
  have hb:(select x).val 0∈hubMarkedCycleVertices u C:=by
    rw [hroot]
    exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩
  exact Finset.disjoint_left.mp hdis ha hb
end Oberwolfach
