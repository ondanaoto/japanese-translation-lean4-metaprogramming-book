import Lean
open Lean Elab Command
/-!
# Elaboration
--todo
* `TermElabM` etc.
* elaboration attributes (for commands, tactics)
* postponed metas
* macros

The elaborator is the component in charge of turning the user facing
`Syntax` into something rest of the compiler can work with. Most of the
time this means translating `Syntax` into `Expr`s but there are also
other use cases such as `#check` or `#eval`. Hence the elaborator is
quite a large piece of code, it lives
[here](https://github.com/leanprover/lean4/blob/master/src/Lean/Elab).
-/

/-!
## Command elaboration
A command is the highest level kind of `Syntax`. A Lean file is made
up of a list of commands. The most commonly used ones being declarations,
for example:
- `def`
- `inductive`
- `structure`
but there are also other ones, most notably `#check`, `#eval` and friends.

### The Monad stack
Like almost all meta code command elaboration is based on a Monad stack
that lives [here](https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/Command.lean):
-/
namespace Playground

structure State where
  env            : Environment
  messages       : MessageLog := {}
  scopes         : List Scope := [{ header := "" }]
  nextMacroScope : Nat := firstFrontendMacroScope + 1
  maxRecDepth    : Nat
  nextInstIdx    : Nat := 1
  ngen           : NameGenerator := {}
  infoState      : InfoState := {}
  traceState     : TraceState := {}
  deriving Inhabited

structure Context where
  fileName       : String
  fileMap        : FileMap
  currRecDepth   : Nat := 0
  cmdPos         : String.Pos := 0
  macroStack     : MacroStack := []
  currMacroScope : MacroScope := firstFrontendMacroScope
  ref            : Syntax := Syntax.missing
  tacticCache?   : Option (IO.Ref Tactic.Cache)

abbrev CommandElabCoreM (ε) := ReaderT Context $ StateRefT State $ EIO ε
abbrev CommandElabM := CommandElabCoreM Exception
abbrev CommandElab  := Syntax → CommandElabM Unit

end Playground
/-!
As you can see it's a very normal monad stack meta world, it provides us
with some `Context` to work with as well as a `State` to modify and is capable
of throwing `Exception`s. A thing that is different though, is that the type of
command elaborators, `CommandElab`, is a function from the user `Syntax` to
a `Unit` value wrapped inside the `CommandElabM` monad. This means that we are
executing command elaborators merely for the sake of their effect on their state,
so lets take a closer look at its fields:
- `env` provides us with an `Environment`, one of the most central datastructures
  in the Lean compiler, this is where all declarations and many other things are stored.
  So if a user makes a new declaration via, for example, a `def`, this is
  where its value will be stored.
- `messages` contains all the messages generated by a command, this is how
  `#eval` tells us the output of something we gave it.
- `scopes` Is the means by which Lean manages (surprise) scopes,
  here things like values bound by the `variable` command, the current
  namespace etc. are stored.
- `nextMacroScope` is relevant for macro expansion which will be discussed
  at length in another section.
- `maxRecDepth` is the maximum amount of times we may recurse into other
  elaborators during execution so we break at some point. 
- `nextInstIdx` is used to generate automatically named `instance`s
- `ngen` is used to generate new unique names
- `infoState` is used for `InfoTree` generation which in turn is related
  to the Lean LSP integration.
- `traceState` is similar to `messages` but only used for the Lean internal
  `trace` infrastructure.
As explained before there is also some read only `Context` we have access to,
its fields are not that important but lets take a quick look:
- `fileName`, quite obviously the name of the file this command is being elaborated in
- `fileMap`, contains informations about the source code of the file that is being elaborated
- `currRecDepth` the value that is capped by `maxRecDepth`
- `cmdPos` the position of the command that is being elaborted
- `macroStack`, `currMacroScope` again used for macro expansion, discussed later on
- `ref`, describes the syntactic position of the command that is being elaborated,
  most commonly used for positioning of error messages
- `tacticCache?`, quite obviously a cache for tactic evaluation

### How it works
Now that we understand the type of command elaborators let's take a closer
look to how the elaboration process actually works. The entry point for the
Lean compiler is `elabCommandTopLevel` but as its doc string says its a:
"`elabCommand` wrapper that should be used for the initial invocation, not
for recursive calls after macro expansion etc." So the function we are
actually interested in is `elabCommand`. The way it works is actually rather simple:
1. If we are elaborating a `Syntax` with a list of commands simply elaborate all of them
   in order.
2. Otherwise check whether any macros can be applied to the current `Syntax` via
   `expandMacroImpl?`. Macros will be discussed at length below but for now you
   can just think of them as `Syntax -> Syntax` functions. If we find a macro
   that does apply and does not throw an error we recursively elaborate the
   resulting command `Syntax` with `elabCommand`
3. If no macro can be applied we search for all `CommandElab`s that have been
   registered for the `SyntaxKind` of the `Syntax` we are elaborating, using the `commandElabAttribute`.
   All of these `CommandElab` are then tried in order until one of them does not throw an
   `unsupportedSyntaxEception`, this indicates that the elaborator "feels responsible"
   for this specific `Syntax` construct. Note that it can still throw a regular
   error to indicate to the user that something is wrong. If no responsible
   elaborator is found the command elaboration is aborted with a `unexpected syntax`
   error message.
Note that this is just a rough description that doesnt go into the details about the
`InfoTree` handling that is happening during this process, since they are not relevant
for a general understanding of what is going on.


### Making our own
Now that we know both what a `TermElab` is and how they are used we can
start into looking to write our own. The steps for this are:
1. Declaring our Syntax
2. Declaring the elaborator
3. Registering the elaborator as responsible for the syntax via `commandElabAttribute`
Lets see how this is done
-/
syntax (name := mycommand1) "#mycommand1" : command -- declare the syntax

@[commandElab mycommand1] def mycommand1Impl : CommandElab := fun stx => do -- declare and register the elaborator
  logInfo "Hello World"

#mycommand1

/-!
You might think that this is a little boiler-platey and it turns out the Lean
devs did as well so they added a macro for this!
-/
elab "#mycommand2" : command =>
  logInfo "HelloWorld"

#mycommand2

/-!
Note that due to the fact that command elaboration supports multiple
registered elaborators for the same syntax we can in fact overload
syntax if we want to.
-/
@[commandElab mycommand1] def myNewImpl : CommandElab := fun stx => do
  logInfo "new!"

#mycommand1

/-!
Furthermore it is also possible to only overload parts of syntax by
throwing an `unsupportedSyntaxException` in the cases we want the default
handler to deal with or just letting the `elab` command handle it
-/

/-
Note that this is not extending the original #check syntax but adding a new SyntaxKind
for this specific syntax construct, however it behaves basically the same to the user.
-/
elab "#check" "foo" : command => do
  logInfo "Got ya!"

@[commandElab Lean.Parser.Command.check] def mySpecialCheck : CommandElab := fun stx => do
  if let some str := stx[1].isStrLit? then
    logInfo s!"Specialy elaborated string literal!: {str} : String"
  else
    throwUnsupportedSyntax

#check foo
#check "Hello"
#check Nat.add

/-!
As a final mini project for this section let's build a command elaborator
that is actually useful. It will take a command and use the same mechanisms
as `elabCommand` to tell us which macros or elaborators are relevant to the
command we gave it (we will not go through the effort of actually reimplementing
`elabCommand` though).
-/
elab "#findCElab " c:command : command => do
  let macroRes ← liftMacroM <| expandMacroImpl? (←getEnv) c
  match macroRes with
  | some (name, _) => logInfo s!"Next step is a macro: {name.toString}"
  | none =>
    let kind := c.getKind
    let elabs := commandElabAttribute.getEntries (←getEnv) kind
    match elabs with
    | [] => logInfo s!"There is no elaborators for your syntax, looks like its bad :("
    | _ => logInfo s!"Your syntax may be elaborated by: {elabs.map (fun el => el.declName.toString)}"

#findCElab def lala := 12
#findCElab abbrev lolo := 12
#findCElab #check foo -- even our own syntax!
#findCElab open Hi
#findCElab namespace Foo
#findCElab #findCElab open Bar -- even itself!

/-!
## Term elaboration
-/

/-!
## Macros
-/
