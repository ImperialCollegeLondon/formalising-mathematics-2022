import algebra.category.Module.basic
/-!

# Picard group of a commutative ring

Done with categories.

-/

universe u

/-

If `R` is a ring in universe `u`, then
`Module.{u u} R` is the category of `R`-modules
in universe `u`.

-/

variables (R : Type u) [comm_ring R]

open category_theory

def Module.one : Module.{u u} R := Module.of R R

-- We're isomorphic
def s : setoid (Module.{u u} R) :=
{ r := λ M N, nonempty (M ≅ N),
  iseqv := begin
    sorry,
  end }