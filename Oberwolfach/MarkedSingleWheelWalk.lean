module

public import Oberwolfach.MarkedSingleWheelPhysicalPath

@[expose] public section
/-! Represent the physical rim of one marked wheel as a simple graph walk. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_single_wheel_physical_walk
    {V E K:Type*} (G:SimpleGraph V) (tail head:E→V) (ktail khead:K→V)
    (m b:ℕ) (π:Equiv.Perm V) (hb:1≤b)
    (C:MarkedCycleTuple tail head ktail khead m π b)
    (hroot:π (C.val 0)≠C.val 0)
    (hE:∀e:E,G.Adj (tail e) (head e))
    (hK:∀e:K,G.Adj (ktail e) (π (khead e))):
    ∃f:Fin ((m+1)+1)↪V,
      (∀i:Fin (m+1),f i.castSucc=C.val i) ∧ f (Fin.last (m+1))=π (C.val 0) ∧
      ∃p:G.Walk (C.val 0) (π (C.val 0)),
        p.IsPath ∧ p.length=m+1 ∧ p.support=List.ofFn f := by
  obtain ⟨f,hprefix,hlast,hadj⟩:=marked_single_wheel_physical_path G tail head ktail khead m b π hb C hroot hE hK
  have h0:(⟨0,by omega⟩:Fin ((m+1)+1))=(0:Fin ((m+1)+1)):=by apply Fin.ext; rfl
  have hfin:(⟨m+1,by omega⟩:Fin ((m+1)+1))=Fin.last (m+1):=by apply Fin.ext; rfl
  have hfirst:f (0:Fin ((m+1)+1))=C.val 0:=by simpa using hprefix 0
  obtain ⟨p,hp,hlen,hsupp⟩:=finite_sequence_simple_walk G (m+1) f hadj
  refine ⟨f,hprefix,hlast,?_⟩
  have hf0:f ⟨0,by omega⟩=C.val 0:=by rw [h0];exact hfirst
  have hfn:f ⟨m+1,by omega⟩=π (C.val 0):=by rw [hfin];exact hlast
  rw [←hfn,←hf0]
  exact ⟨p,hp,hlen,hsupp⟩
end Oberwolfach
