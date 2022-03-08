import tactic
import linear_algebra.tensor_product
import algebra.category.Module.basic

-- Picard groups via modules

universe u

variables (R : Type u) [comm_ring R]

variables (V : Type u) [add_comm_group V] [module R V]

example : Module R := Module.of R V 

-- notation for tensor product
open_locale tensor_product

def Module.mul (M N : Module.{u u} R) : Module R :=
Module.of R (M ⊗[R] N)

variables (A B : Module.{u u} R)

instance : has_mul (Module.{u u} R) :=
{ mul := Module.mul R }

instance : has_one (Module.{u u} R) :=
{ one := Module.of R R }

#check A * B 

open category_theory


#check @forall_congr

#check @tensor_product.congr

def module.s : con (Module.{u u} R) :=
{ r := λ M N, nonempty (M ≅ N),
  iseqv := begin
    refine ⟨_, _, _⟩,
    { intro M,
      exact nonempty.intro (iso.refl M) },
    sorry, sorry
  end,
  mul' := begin
    rintros A B C D ⟨hAB⟩ ⟨hCD⟩,
    replace hAB := iso.to_linear_equiv hAB,
    replace hCD := iso.to_linear_equiv hCD,
    let hABCD := tensor_product.congr hAB hCD,
    apply nonempty.intro,
    exact linear_equiv.to_Module_iso hABCD,
  end }

abbreviation Module.Picard_monoid := (module.s R).quotient

instance : has_mul (Module.Picard_monoid R) := infer_instance

instance : monoid (Module.Picard_monoid R) :=
{ mul := (*),
  mul_assoc := sorry,
  one := sorry,
  one_mul := sorry,
  mul_one := sorry,
}

#check (Module.Picard_monoid R)

abbreviation Module.Picard_group := units (Module.Picard_monoid R)

instance : group (Module.Picard_group R) := infer_instance

#check (Module.Picard_group R)
