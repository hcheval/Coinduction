import Mathlib

-- #check Finset.induction_on
inductive T where
| bot : T
| tree : List T → T

#print T.rec

#check Thunk



example (t : T) : False := by
  induction t
