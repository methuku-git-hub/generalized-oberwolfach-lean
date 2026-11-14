module

public import Oberwolfach.MarkedEmbeddedHubCycles

@[expose] public section

/-! Common marked paths inside an invariant inner domain inject into the
ambient host without restoring any omitted root spokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {W V U E K:Type} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]

def hubPathEmbedding (f:W↪V) (ρ:Equiv.Perm W) (π:Equiv.Perm V)
    (h:∀ x,f (ρ x)=π (f x)) (tail head:E→W) (ktail khead:K→W)
    (m b:ℕ) (H₀ HK:W→U→Prop) (j:Bool) (x x':W) (u u':U):
    RootFirstCommonMarkedPath tail head ktail khead m ρ b H₀ HK j x x' u u'↪
      RootFirstCommonMarkedPath (f∘tail) (f∘head) (f∘ktail) (f∘khead) m π b
        (spokeRelationImage f H₀) (spokeRelationImage f HK) j (f x) (f x') u u' where
  toFun C:=by
    have he (v:W):Fin.cases (f v) (f∘C.val)=f∘Fin.cases v C.val:=by
      funext i
      refine Fin.cases ?_ (fun i=>?_) i <;> rfl
    refine ⟨f∘C.val,?_,?_,?_⟩
    · rw [he]
      exact (rootFirstMarkedCycle_embedding_iff f ρ π h tail head ktail khead m b _ _).mpr C.property.1
    · rw [he]
      exact (rootFirstMarkedCycle_embedding_iff f ρ π h tail head ktail khead m b _ _).mpr C.property.2.1
    · intro i
      have hh:=C.property.2.2 i
      simp only [Function.comp_apply]
      split_ifs at hh ⊢ <;> exact ⟨⟨_,rfl,hh.1⟩,⟨_,rfl,hh.2⟩⟩
  inj' C D he:=by
    apply Subtype.ext
    funext i
    exact f.injective (congrArg (fun C=>C.val i) he)

theorem hubPathEmbedding_card (f:W↪V) (ρ:Equiv.Perm W) (π:Equiv.Perm V)
    (h:∀ x,f (ρ x)=π (f x)) (tail head:E→W) (ktail khead:K→W)
    (m b:ℕ) (H₀ HK:W→U→Prop) (j:Bool) (x x':W) (u u':U):
    Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m ρ b H₀ HK j x x' u u')≤
      Fintype.card (RootFirstCommonMarkedPath (f∘tail) (f∘head) (f∘ktail) (f∘khead) m π b
        (spokeRelationImage f H₀) (spokeRelationImage f HK) j (f x) (f x') u u'):=
  Fintype.card_le_of_injective _ (hubPathEmbedding f ρ π h tail head ktail khead m b H₀ HK j x x' u u').injective

end Oberwolfach
