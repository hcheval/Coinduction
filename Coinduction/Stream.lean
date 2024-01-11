import Mathlib

def Stream' := List 

instance (α : Type) [PartialOrder α] : PartialOrder (List α) := inferInstance