module

public import Oberwolfach.FirstVortexMatchingScale
public import Oberwolfach.FirstVortexNonempty

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem Vortex.first_inner_vertex_size_lower_of_positive_terminal_size
    {V U:Type} [Fintype V] [Fintype U] {G:SimpleGraph V}
    {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m) (he:0<ε) (hm:0<m):
    ε*(Fintype.card V:ℝ)/2≤(Q.extendedVertices 1).card:=
  Q.first_inner_vertex_size_lower he (Q.first_inner_vertex_nonempty he hm)
end Oberwolfach
