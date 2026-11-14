module

public import Oberwolfach.CommonClassBalanceBounds
public import Oberwolfach.PermutationClose

@[expose] public section

/-! The class disjointness and successor exclusion used in balancing,
derived from the two spoke types and separation of prescribed roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [DecidableEq V]

 theorem common_class_spoke_disjoint (H₀ HK:V→U→Prop) (u:U)
    (hdis:∀ v,HK v u→¬H₀ v u) (A₀ B₀ ZO:Finset V)
    (hA:∀ v∈A₀,HK v u) (hB:∀ v∈B₀,H₀ v u) (hZO:∀ v∈ZO,H₀ v u):
    Disjoint A₀ (B₀∪ZO):=by
  apply Finset.disjoint_left.mpr
  intro v hv hh
  rcases Finset.mem_union.mp hh with hh|hh
  · exact hdis v (hA v hv) (hB v hh)
  · exact hdis v (hA v hv) (hZO v hh)

 theorem separated_root_successor_disjoint (π:Equiv.Perm V) (b:ℕ) (hb:1≤b)
    (ZK ZO:Finset V) (hdis:Disjoint ZK ZO)
    (hsep:∀ x∈ZK∪ZO,∀ y∈ZK∪ZO,x≠y→¬PermutationClose π b x y):
    Disjoint ZK (ZO.image π.symm):=by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨y,hy,he⟩:=Finset.mem_image.mp hy
  have hne:x≠y:=fun h=>Finset.disjoint_left.mp hdis hx (h ▸ hy)
  apply hsep x (Finset.mem_union_left _ hx) y (Finset.mem_union_right _ hy) hne
  apply Or.inr
  refine ⟨⟨0,by omega⟩,Or.inl ?_⟩
  have hh:π x=y:=by rw [←he,π.apply_symm_apply]
  simpa only [Nat.zero_add,pow_one] using hh

end Oberwolfach
