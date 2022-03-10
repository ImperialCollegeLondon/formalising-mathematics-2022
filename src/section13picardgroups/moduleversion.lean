import tactic
import linear_algebra.tensor_product
import algebra.category.Module.basic

-- Picard groups via the category `Module R` of R-modules.

universe u

variables (R : Type u) [comm_ring R]

variables (V : Type u) [add_comm_group V] [module R V]

example : Module R := Module.of R V 

-- enable notation for tensor product
open_locale tensor_product

def Module.mul (M N : Module.{u u} R) : Module R :=
Module.of R (M ⊗[R] N)

variables (A B : Module.{u u} R)

instance : has_mul (Module.{u u} R) :=
{ mul := Module.mul R }

instance : has_one (Module.{u u} R) :=
{ one := Module.of R R }

open category_theory

def module.s : con (Module.{u u} R) :=
{ r := λ M N, nonempty (M ≅ N),
  iseqv := begin
    refine ⟨_, _, _⟩,
    { intro M,
      exact nonempty.intro (iso.refl M) },
    { intros M N hMN, 
      exact nonempty.map iso.symm hMN },
    { rintros M N P ⟨hMN⟩ ⟨hNP⟩,
      exact nonempty.intro (hMN.trans hNP) },
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
  mul_assoc := begin
    intros a b c,
    apply quotient.induction_on₃' a b c, clear a b c,
    intros M N P,
    apply quotient.sound',
    exact ⟨linear_equiv.to_Module_iso (tensor_product.assoc R ↥M ↥N ↥P)⟩,
  end,
  one := quotient.mk' 1,
  one_mul := begin
    intro a, apply quotient.induction_on' a, clear a,
    intro M,
    apply quotient.sound',
    apply nonempty.intro,
    suffices : M ≅ Module.of R M,
    { refine iso.trans _ this.symm,
      convert (tensor_product.lid R M).to_Module_iso },
    cases M,
    apply linear_equiv.to_Module_iso,
    convert (linear_equiv.refl R _),
  end,
  mul_one := begin
    intro a, apply quotient.induction_on' a, clear a,
    intro M,
    apply quotient.sound',
    apply nonempty.intro,
    suffices : M ≅ Module.of R M,
    { refine iso.trans _ this.symm,
      convert (tensor_product.rid R M).to_Module_iso },
    cases M,
    apply linear_equiv.to_Module_iso,
    convert (linear_equiv.refl R _),
  end,
}

abbreviation Module.Picard_group := units (Module.Picard_monoid R)

instance : group (Module.Picard_group R) := infer_instance

#check (Module.Picard_group R) -- Type (u + 1) because 
-- the collection of all modules over a ring "isn't a set"
  
