module

public import Oberwolfach.PrescribedSubtypeCompleteGlue

@[expose] public section
/-! Selected anchor images avoid reserved labels outside the final paths,
without asking the prescribed path endpoints themselves to avoid those labels. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selected_anchors_avoid_reserved_outside
    {X V:Type} [DecidableEq X] [DecidableEq V]
    (A B:Finset X) (f g Φ:X→V) (C Z Y:Finset V) (outside:X→Prop)
    (hAB:A⊆B) (hΦ:Function.Injective Φ)
    (hg:∀x∈A,g x=f x) (hΦg:∀x∈B,Φ x=g x)
    (himage:B.image g=A.image f∪C∪Z)
    (hOld:∀x∈A,outside x→f x∉Y)
    (hC:Disjoint C Y) (hZ:Disjoint Z Y):
    ∀x∈B,outside x→g x∉Y:=by
  intro x hx hout hxy
  have him:g x∈A.image f∪C∪Z:=by
    rw [←himage]
    exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
  rcases Finset.mem_union.mp him with holdOrC | hz
  · rcases Finset.mem_union.mp holdOrC with hold | hc
    · obtain ⟨y,hy,heq⟩:=Finset.mem_image.mp hold
      have hxy':Φ x=Φ y:=by rw [hΦg x hx,hΦg y (hAB hy),hg y hy];exact heq.symm
      have hsame:x=y:=hΦ hxy'
      subst y
      exact hOld x hy hout (by rwa [←hg x hy])
    · exact Finset.disjoint_left.mp hC hc hxy
  · exact Finset.disjoint_left.mp hZ hz hxy
end Oberwolfach
