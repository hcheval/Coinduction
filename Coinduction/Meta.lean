import Lean
import Mathlib

open Lean

set_option autoImplicit false

open Lean.Elab.Command (CommandElabM)

def addDecl (decl : Declaration) : CommandElabM PUnit := do
  match (← getEnv).addAndCompile {} decl with
  | .error e => throwError e.toMessageData default
  | .ok env => setEnv env

-- is this the way? why does the builtin one live in `CoreM`?
def mkArrow (e₁ e₂ : Expr) : Expr :=
  mkForall .anonymous .default e₁ e₂

elab "nat" : command => do
  let decl : Declaration :=
    mkInductiveDeclEs
      (lparams := [])
      (nparams := 0)
      (isUnsafe := false)
      (types := [{
        name := `MyNat
        type := mkSort Level.zero.succ
        ctors := [{
          name := `MyNat ++ `zero
          type := mkConst `MyNat
        },
        {
          name := `MyNat ++ `succ
          type := mkArrow (mkConst `MyNat) (mkConst `MyNat)
        }]
      }])
  addDecl decl

nat

#print MyNat
inductive T

elab "gen" id:ident : command => do
  let univ : Name := `u
  let type : Expr := mkSort <| mkLevelSucc <| mkLevelParam univ
  let decl : Declaration :=
    mkInductiveDeclEs
      (lparams := [univ])
      (nparams := 1)
      (isUnsafe := false)
      (types := [{
        name := id.getId
        type := mkForall .anonymous .default type type
        ctors := [{
          name := id.getId ++ `mk
          type := mkForall `α .implicit type <| mkForall `x .default (mkBVar 0) <| mkApp (mkConst id.getId [mkLevelParam `u]) (mkBVar 1)
        }]
      }])
  match (← getEnv).addAndCompile {} decl with
  | .error w => throwError "error"
  | .ok env => setEnv env

-- gen A
-- #print A
-- def a : A Nat := A.mk 1

-- -- elab "gen_structure" id:ident : command => do
-- --   let type_u := mkSort (mkLevelSucc (mkLevelParam `u))
-- --   let decl := mkInductiveDeclEs [`u] 1 [{
-- --     name := id.getId
-- --     type := mkForall .anonymous .default type_u type_u
-- --     ctors := [{
-- --       name := id.getId ++ `mk
-- --       type :=
-- --         mkForall `α .implicit type_u
-- --         <| mkForall `x .default (mkBVar 0)
-- --         <| mkApp (mkConst id.getId [mkLevelParam `u]) (mkBVar 1)
-- --     }]
-- --   }] false
-- --   match (← getEnv).addAndCompile {} decl with
-- --   | .error e => throwError ("addAndCompile error: " ++ e.toMessageData {})
-- --   | .ok env => setEnv env

-- -- gen_structure A


-- -- open Lean Elab Command Term Meta

-- -- syntax (name := codata) "codata" ident "where" many(Lean.Parser.Command.ctor) : command

-- open Lean Parser Command in
-- @[command_parser] def codata      := leading_parser
--   "codata " >> declId >> ppIndent optDeclSig >> Parser.optional (symbol " :=" <|> " where") >>
--   many ctor >> Parser.optional (ppDedent ppLine >> computedFields) >> optDeriving

-- -- open Lean.Parser.Command in
-- -- @[command_parser] def codata_parser := leading_parser
-- --   "codata" >> declId

-- @[command_elab «codata»]
-- def elabCo : Lean.Elab.Command.CommandElab := fun stx => do
--   let decl := stx[4]
--   IO.println decl

-- codata A where | mk : A → A

-- #check Elab.Command.elabInductiveViews


-- #check Lean.Elab.DerivingHandler
-- -- open Lean Parser Command in
-- -- @[command_parser] def p := leading_parser "#p " >> declId

-- -- syntax (name := mycommand1) "#mycommand1" : command -- declare the syntax

-- -- @[command_elab mycommand1]
-- -- def mycommand1Impl : Lean.Elab.Command.CommandElab := fun stx => do -- declare and register the elaborator
-- --   logInfo "Hello World"
-- -- #check Elab.Command.InductiveView
-- -- #mycommand1 -- Hello World

----------------------------------------------------------------------------------------------------------------------------------

open Lean Elab Command

def getCtors (modifiers : Modifiers) (decl : Syntax) : CommandElabM <| Array CtorView := do
  let declId := decl[1]
  let ⟨_, declName, _⟩ ← expandDeclId declId modifiers
  let ctors      ← decl[4].getArgs.mapM fun ctor => withRef ctor do
    -- def ctor := leading_parser optional docComment >> "\n| " >> declModifiers >> rawIdent >> optDeclSig
    let mut ctorModifiers ← elabModifiers ctor[2]
    if let some leadingDocComment := ctor[0].getOptional? then
      if ctorModifiers.docString?.isSome then
        logErrorAt leadingDocComment "duplicate doc string"
      ctorModifiers := { ctorModifiers with docString? := TSyntax.getDocString ⟨leadingDocComment⟩ }
    if ctorModifiers.isPrivate && modifiers.isPrivate then
      throwError "invalid 'private' constructor in a 'private' inductive datatype"
    if ctorModifiers.isProtected && modifiers.isPrivate then
      throwError "invalid 'protected' constructor in a 'private' inductive datatype"
    checkValidCtorModifier ctorModifiers
    let ctorName := ctor.getIdAt 3
    let ctorName := declName ++ ctorName
    let ctorName ← withRef ctor[3] <| applyVisibility ctorModifiers.visibility ctorName
    let (binders, type?) := expandOptDeclSig ctor[4]
    addDocString' ctorName ctorModifiers.docString?
    addAuxDeclarationRanges ctorName ctor ctor[3]
    return { ref := ctor, modifiers := ctorModifiers, declName := ctorName, binders := binders, type? := type? : CtorView }
  return ctors

#check Syntax.instToStringSyntax
#check SourceInfo
open Lean Parser Command
def getBotCtor (modifiers : Modifiers) (decl : Syntax) : CommandElabM CtorView := do
  let declId := decl[1]
  let ⟨_, declName, _⟩ ← expandDeclId declId modifiers
  let ctorName := `bot
  let ctorName := declName ++ ctorName
  let binders : Syntax := Syntax.atom default ""
  let type? : Option Syntax := none
  return { ref := default, modifiers := default, declName := ctorName, binders := binders, type? := type? }

def inductiveSyntaxToView (modifiers : Modifiers) (decl : Syntax) : CommandElabM InductiveView := do
  checkValidInductiveModifier modifiers
  let (binders, type?) := expandOptDeclSig decl[2]
  let declId           := decl[1]
  let ⟨name, declName, levelNames⟩ ← expandDeclId declId modifiers
  addDeclarationRanges declName decl
  let ctors      ← getCtors modifiers decl
  let ctors := ctors.push (← getBotCtor modifiers decl)
  let computedFields ← (decl[5].getOptional?.map (·[1].getArgs) |>.getD #[]).mapM fun cf => withRef cf do
    return { ref := cf, modifiers := cf[0], fieldId := cf[1].getId, type := ⟨cf[3]⟩, matchAlts := ⟨cf[4]⟩ }
  let classes ← getOptDerivingClasses decl[6]
  return {
    ref             := decl
    shortDeclName   := name
    derivingClasses := classes
    declId, modifiers, declName, levelNames
    binders, type?, ctors
    computedFields
  }


@[command_parser] def data     := leading_parser
  "data " >> declId >> ppIndent optDeclSig >> Parser.optional (symbol " :=" <|> " where") >>
  many ctor >> Parser.optional (ppDedent ppLine >> computedFields) >> optDeriving



open Lean Elab Command in
@[command_elab «data»] def elabCodata : CommandElab := fun stx => do
  let decl := stx
  let modifiers := ({} : Modifiers)
  -- dbg_trace decl
  let view ← inductiveSyntaxToView modifiers decl
  -- IO.println decl[4].getArgs
  elabInductiveViews #[view]

data CoNat where
| zero
| succ : CoNat → CoNat

data Str (α : Type) where
| cons : α → Str α → Str α

#check Str.bot








------------------------------------------------------------------------------------

-- open Lean.Parser.Command (ctor)

-- syntax (name := codata) "codata" ident "where" ctor* : command

-- @[command_elab «codata»] def elabCodata : CommandElab := fun stx => do
--   dbg_trace stx[3]
--   -- match stx with
--   -- | `(command| codata $id:ident where $ctors:ctor*) =>
--   --   let a := ctors.toList[0]!

--   -- | _ => throwUnsupportedSyntax

-- codata A where | mk : A → A| mk : A → A


------------------------------------------------------------------------------------------

-- open Lean Parser Command in
-- set_option hygiene false in
-- macro "codata" id:ident "where" ctors:ctor* : command =>
--   `(command| inductive $id:ident where $ctors:ctor* | bot)

-- codata CoNat where
-- | zero : CoNat
-- | succ : CoNat → CoNat

-- codata Str where
-- | cons :

-- #check CoNat.bot





-----------------------------------------------------------------------------------------------

-- macro mods:declModifiers "lemma" n:declId sig:declSig val:declVal : command => `($mods:declModifiers theorem $n $sig $val)

-- -- set_option hygiene false in
-- macro "fuel" id:declId sig:optDeclSig ":=" val:term : command => do
--   let n := `fuel ++ id.raw[0].getId
--   let n' := Lean.mkIdent <| toString n
--   dbg_trace n
--   `(
--     def $id $sig := $val
--     def $n' := 0
--   )

-- open Term

-- -- syntax (name := abstract) "abstract" funBinder ":=" term : command

-- -- @[command_elab «abstract»] def elabAbstract : CommandElab := fun stx => liftTermElabM do
-- --   match stx with
-- --   | `(command| abstract $id := $body) =>
-- --     let body ← elabTermAndSynthesize body none
-- --     dbg_trace body
-- --   | _ => throwUnsupportedSyntax

-- open Lean.Expr

-- #check Lean.Meta.forallMetaBoundedTelescope

-- def isNotDependentForall (e : Expr) : Bool := !(e.isForall && !e.isArrow)
-- def isDependentForall (e : Expr) : Bool := e.isForall && !e.isArrow



-- def getDependentForallBody (e : Expr) : MetaM Expr := do
--   let mut body := e
--   while isDependentForall body do
--     body := (← Lean.Meta.forallMetaBoundedTelescope e 1).2.2
--   return body


-- def getUnderlyingType (e : Expr) : Option Expr :=
--   return getForallBody e


-- syntax (name := partdef) "partdef" Lean.Parser.ident ":" term ":=" term : command

-- -- @[command_elab «partdef»] def elabPartdef : CommandElab := fun stx =>
-- --   liftTermElabM do
-- --     dbg_trace stx[1].getId
-- --     let name := stx[1].getId
-- --     let type ← elabTermAndSynthesize stx[3] none
-- --     dbg_trace ← getDependentForallBody type
-- --     dbg_trace type
-- --     let value ← elabTermAndSynthesize stx[5] type
-- --     dbg_trace value
-- --     let decl : Declaration := .defnDecl {
-- --       name := name
-- --       levelParams := []
-- --       type := type
-- --       value := value
-- --       hints := .regular (getMaxHeight (← getEnv) value + 1)
-- --       safety := .safe
-- --     }
-- --     addDecl decl

-- -- whatsnew in
-- -- partdef Ever : ∀ {α β : Type}, (α → List α) → α → List α := fun ever => (fun n => n :: ever n)

open Lean Parser Term
set_option hygiene false in
macro "functional" id:funBinder ":=" val:term : command =>
  let functionalId := Lean.mkIdent <| toString <| `Func ++ id.raw[1].getId
  let type : TSyntax `term := ⟨id.raw[3]⟩
  dbg_trace type
  let fuelId := Lean.mkIdent <| toString <| `Fuel ++ id.raw[1].getId
  `(
    def $functionalId := fun $id => $val
  )

open Lean Parser Term in
set_option hygiene false in
macro "part" id:Parser.ident ":" type:term ":=" val:term : command =>
  let functionalId := Lean.mkIdent <| toString <| `Func ++ id.raw[1].getId
  let type : TSyntax `term := ⟨id.raw[3]⟩
  `(
    def $functionalId := fun ($id : $type) => $val
  )



-- @[command_elab «partdef»] def elabPartdef : CommandElab := fun stx => do
--   match stx with
--   | `(command| partdef $id : $type := $val) =>
--     -- let idType : funBinder := _
--     dbg_trace id
--     dbg_trace type
--     dbg_trace val
--     elabCommand <| ← `(functional ($id : $type) := $val)
--   | _ => throwUnsupportedSyntax

-- -- functional (x : Nat) := x

-- whatsnew in
-- partdef f : Nat → Nat := fun (n : Nat) => f n



-- -- set_option hygiene false in
-- -- macro "functional" id:declId ":=" val:term : command =>
-- --   let binder : TSyntax `Lean.Parser.Term.funBinder := ⟨mkExplicitBinder (mkIdent <| id.raw[0].getId) ""⟩
-- --   `(def a := fun $binder => $val)

-- def withFuel {α β : Type} (F : (α → Option β) → α → Option β) : Nat → α → Option β :=
--   fun n a => match n with
--   | 0 => none
--   | n + 1 => F (withFuel F n) a

-- whatsnew in
-- functional (collatz : ℕ → Option (List ℕ)) :=
--   fun n => do if n = 1 then return [1] else if Even n then n :: (← collatz (n / 2)) else n :: (← collatz (3 * n + 1))

-- whatsnew in
-- functional (f : α → Option β) :=
--   fun a => do return ← f a

-- whatsnew in
-- functional (ever : ℕ → ℕ → List ℕ) :=
--   fun n m => n :: m :: ever n m

-- -- whatsnew in
-- -- fuel f := 3

-- #check «fuel.f»




---------------------------------------------------------------------------

abbrev Fuel := ℕ

def withFuel {α β : Type} (F : (α → Option β) → α → Option β) : Fuel → α → Option β :=
  fun n a => match n with
  | 0 => none
  | n + 1 => F (withFuel F n) a

syntax (name := partdef) "partdef" Parser.ident ":" term ":=" term : command

-- open Lean Meta in
-- def mkFunctional (name : Name) (body : Expr) (type : Expr) : MetaM Expr :=
--   withLocalDecl name .default type (fun e => do mkLambdaFVars #[e] body)

def mkFunctionalName (name : Name) : Name :=
  name ++ `functional

def mkWithFuelName (name : Name) : Name :=
  name ++ `fueled

open Lean Meta in
def addFunctional (name : Name) (type : TSyntax `term) (val : TSyntax `term) : TermElabM Unit := do
  let type ← elabTermAndSynthesize type none
  let value ← withLocalDecl name .default type <| fun e => do
    let body ← elabTermAndSynthesize val none
    mkLambdaFVars #[e] body
  let decl := Declaration.defnDecl {
    name := mkFunctionalName name
    levelParams := []
    type := ← Lean.mkArrow type type
    value := value
    hints := .regular <| getMaxHeight (← getEnv) value + 1
    safety := .safe
  }
  addDecl decl

#print Expr

def addWithFuel (name : Name) (type : Expr) : TermElabM Unit := do
  let decl := Declaration.defnDecl {
    name := mkWithFuelName name
    levelParams := []
    type := ← Lean.mkArrow (mkConst `Fuel []) type
    value := ← Meta.mkAppM (`withFuel) #[mkConst (mkFunctionalName name) []]
    hints := default
    safety := .safe
  }
  addDecl decl

#print Command.declId
open Lean Elab Term
@[command_elab «partdef»] def elabPartdef : CommandElab := fun stx =>
liftTermElabM do
  match stx with
  | `(command| partdef $id:ident : $type:term := $val:term) =>

    addFunctional id.raw.getId type val
    addWithFuel id.raw.getId (← elabTermAndSynthesize type none)
  | _ => throwUnsupportedSyntax
#check elabDeclaration
whatsnew in
partdef x : Nat → Option (List Nat) := fun n => do return n :: (← x n)

whatsnew in
partdef collatz : Nat → Option (List Nat) := fun n => do
  if n == 1 then
    return [1]
  else if Even n then
    return n :: (← collatz (n / 2))
  else
    return n :: (← collatz (3 * n + 1))


#reduce collatz.fueled 10 9

/-
  partdef f : Nat → Nat → List Nat := fun n m => n :: m :: f n m
-/
