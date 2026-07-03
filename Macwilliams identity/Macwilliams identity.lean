import «Macwilliams identity».Basic
open InformationTheory
open scoped InformationTheory
/-! ### Concrete Examples (Sanity Checks) -/
section
def u : Word (ZMod 2) 7 := ![1, 1, 1, 1, 0, 0, 0]
def v : Word (ZMod 2) 7 := ![0, 0, 0, 0, 1, 1, 1]
def l : Word (ZMod 2) 7 := ![1, 1, 1, 1, 1, 1, 1]
def l1 : ZMod 2 := v 4
def l3 : ZMod 2 := v 3
def G : Fin 2 → Word (ZMod 2) 7 := ![u, v]
lemma gen_indep : LinearIndependent (ZMod 2) G := by rw [Fintype.linearIndependent_iff]; decide
def C : LinearCode (ZMod 2) 7 := Submodule.span (ZMod 2) (Set.range G)

#eval l1
#eval l3
#check 2 • v
#check u+v
#eval u+l
#eval 3•v
#eval ‖v‖ₕ
#eval ⟪u,v⟫
#eval ⟪v,l⟫
#eval ⟪u,u⟫
example (ha : u ∈ C) (hb : v ∈ C) : u + v ∈ C := by exact C.add_mem ha hb
#check u+l=v
end
