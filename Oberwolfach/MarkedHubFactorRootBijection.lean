module

public import Oberwolfach.MarkedHubFactorRootSelection

@[expose] public section
/-! In a disjoint hub factor, the selected root map accounts for every
wheel when the marked spokes are exactly the prescribed marked vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_hub_factor_root_bijection
    {V U E K:Type*} [Fintype V] [DecidableEq V]
    (tail head:E→V) (ktail khead:K→V) (m b:ℕ) (π:Equiv.Perm V)
    (H₀ Hₖ:V→U→Prop) (u:U)
    (M:Finset (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u))
    (hM:∀C∈M,∀D∈M,C≠D→Disjoint (hubMarkedCycleVertices u C) (hubMarkedCycleVertices u D))
    (S Y:Finset V) (hcover:M.biUnion (hubMarkedCycleVertices u)=S)
    (hYS:Y⊆S) (hmarked:∀x,Hₖ x u↔x∈Y) (hsep:∀x,Hₖ x u→¬H₀ x u):
    ∃select:{x // x∈Y}↪HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u,
      (∀x,select x∈M ∧ (select x).val 0=x.val) ∧
      (∀C∈M,∃x:{x // x∈Y},select x=C) := by
  obtain ⟨select,hselected⟩:=marked_hub_factor_root_selection tail head ktail khead m b π H₀ Hₖ u M S Y hcover hYS
    (fun x hx=>(hmarked x).2 hx) hsep
  refine ⟨select,hselected,?_⟩
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
