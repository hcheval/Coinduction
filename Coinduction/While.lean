import Mathlib

#print StateT

abbrev Fuel := ℕ

def withFuel {α β : Type} (F : (α → Option β) → α → Option β) : Fuel → α → Option β :=
  fun n a => match n with
  | 0 => none
  | n + 1 => F (withFuel F n) a

partial def collatz_ (n : ℕ) : List ℕ :=
  if n = 1 then
    [1]
  else if Even n then
    n :: collatz_ (n / 2)
  else
    n :: collatz_ (3 * n + 1)


partial def collatz? (n : ℕ) : Option <| List ℕ :=
do
  if n = 1 then
    return [1]
  else if Even n then
    return n :: (← collatz? (n / 2))
  else
    return n :: (← collatz? (3 * n + 1))

#eval collatz?  5

def Collatz (f : ℕ → List ℕ) : ℕ → List ℕ :=
  fun n => if n = 1 then [1] else if Even n then n :: f (n / 2) else n :: f (3 * n + 1)

def Collatz? (f : ℕ → Option (List ℕ)) : ℕ → Option (List ℕ) :=
  fun n =>
    if n = 1 then return [1]
    else if Even n then return n :: (← f (n / 2))
    else return n :: (← f (3 * n + 1))

def collatz₀ : Fuel → ℕ → Option (List ℕ) :=
  withFuel Collatz?

def collatz : (Option Fuel) → ℕ → Option (List ℕ) := _

example : ∀ (fuel : Fuel) (n : ℕ), collatz (some fuel) n = collatz₀ fuel n := sorry

def sum (xs : List Int) : Int := Id.run do
  let mut ret := 0
  for x in xs do
    ret := ret + x
  return ret

#print sum

#check IO

#eval sum [1, 2, 3]
