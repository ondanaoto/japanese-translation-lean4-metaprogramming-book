/-
# Elaboration

The elaborator is the component in charge of turning the user facing
`Syntax` into something with which the rest of the compiler can work.
Most of the time, this means translating `Syntax` into `Expr`s but
there are also other use cases such as `#check` or `#eval`. Hence the
elaborator is quite a large piece of code, it lives
[here](https://github.com/leanprover/lean4/blob/master/src/Lean/Elab).

エラボレータは、ユーザー向けの`Syntax`を
コンパイラの残りの部分が作業できる何かに変換する責任を持つコンポーネントです。
ほとんどの場合、これは`Syntax`を`Expr`に変換することを意味しますが、
`#check`や`#eval`などの他のユースケースもあります。したがって、
エラボレータはかなり大きなコードの塊です。
[ここ](https://github.com/leanprover/lean4/blob/master/src/Lean/Elab)にあります.

## Command elaboration
A command is the highest level of `Syntax`, a Lean file is made
up of a list of commands. The most commonly used commands are declarations,
for example:
- `def`
- `inductive`
- `structure`

コマンドは`Syntax`の最上位レベルであり、Leanファイルはコマンドのリストで構成されています。
最も一般的に使用されるコマンドは、たとえば次のとおりです。
- `def`
- `inductive`
- `structure`

but there are also other ones, most notably `#check`, `#eval` and friends.
All commands live in the `command` syntax category so in order to declare
custom commands, their syntax has to be registered in that category.

しかし、`#check`、`#eval`など、他にも注目すべきコマンドがあります。
すべてのコマンドは`command`構文カテゴリに存在するため、カスタムコマンドを宣言するためには、
その構文がそのカテゴリに登録されていなければなりません。

### Giving meaning to commands
The next step is giving some semantics to the syntax. With commands, this
is done by registering a so called command elaborator.

次のステップは、構文にいくつかのセマンティクスを与えることです。
コマンドについては、いわゆるコマンドエラボレータを登録することによってこれが行われます。

Command elaborators have type `CommandElab` which is an alias for:
`Syntax → CommandElabM Unit`. What they do, is take the `Syntax` that
represents whatever the user wants to call the command and produce some
sort of side effect on the `CommandElabM` monad, after all the return
value is always `Unit`. The `CommandElabM` monad has 4 main kinds of
side effects:
1. Logging messages to the user via the `Monad` extensions
   `MonadLog` and `AddMessageContext`, like `#check`. This is done via
   functions that can be found in `Lean.Elab.Log`, the most notable ones
   being: `logInfo`, `logWarning` and `logError`.
2. Interacting with the `Environment` via the `Monad` extension `MonadEnv`.
   This is the place where all of the relevant information for the compiler
   is stored, all known declarations, their types, doc-strings, values etc.
   The current environment can be obtained via `getEnv` and set via `setEnv`
   once it has been modified. Note that quite often wrappers around `setEnv`
   like `addDecl` are the correct way to add information to the `Environment`.
3. Performing `IO`, `CommandElabM` is capable of running any `IO` operation.
   For example reading from files and based on their contents perform
   declarations.
4. Throwing errors, since it can run any kind of `IO`, it is only natural
   that it can throw errors via `throwError`.

コマンドエラボレータは、`CommandElab`タイプを持ち、
これは`Syntax → CommandElabM Unit`のエイリアスです。
彼らがやることは、ユーザーがコマンドを呼び出すことを望むものを表す`Syntax`を取り、
`CommandElabM`モナドに何らかのサイドエフェクトを生成することです。
結局のところ、返り値は常に`Unit`です。
`CommandElabM`モナドには4つの主要なサイドエフェクトがあります：
1. `#check`のように、`MonadLog`と`AddMessageContext`を介して、
   ユーザーにメッセージを記録する。これは、`Lean.Elab.Log`で見つけることができる関数を介して行われる。
   最も注目すべきものは、`logInfo`、`logWarning`、`logError`です。
2. `MonadEnv`を介して`Environment`と対話する。
    これは、コンパイラのためのすべての関連情報が格納されている場所であり、
    すべての既知の宣言、その型、ドキュメント文字列、値などです。
    現在の環境は`getEnv`を介して取得でき、変更された後に`setEnv`を介して設定できます。
    `setEnv`のようなラッパーを使用することが、
    `Environment`に情報を追加する正しい方法であることに注意してください。
3. `IO`を実行することで、`CommandElabM`は任意の`IO`操作を実行できます。
    たとえば、ファイルから読み取り、その内容に基づいて宣言を行うことができます。
4. エラーをスローすることができます。
    任意の種類の`IO`を実行できるので、`throwError`を介してエラーをスローできるのは当然のことです。

Furthermore there are a bunch of other `Monad` extensions that are supported
by `CommandElabM`:
- `MonadRef` and `MonadQuotation` for `Syntax` quotations like in macros
- `MonadOptions` to interact with the options framework
- `MonadTrace` for debug trace information
- TODO: There are a few others though I'm not sure whether they are relevant,
  see the instance in `Lean.Elab.Command`

さらに、`CommandElabM`がサポートする他のいくつかの`Monad`拡張があります：
- マクロのような`Syntax`引用のための`MonadRef`および`MonadQuotation`
- オプションフレームワークと対話するための`MonadOptions`
- デバッグトレース情報のための`MonadTrace`
- TODO：他にもいくつかありますが、それらが関連しているかどうかはわかりません。
  `Lean.Elab.Command`でインスタンスを参照してください。

### Command elaboration
Now that we understand the type of command elaborators let's take a brief
look at how the elaboration process actually works:
1. Check whether any macros can be applied to the current `Syntax`.
   If there is a macro that does apply and does not throw an error
   the resulting `Syntax` is recursively elaborated as a command again.
2. If no macro can be applied, we search for all `CommandElab`s that have been
   registered for the `SyntaxKind` of the `Syntax` we are elaborating,
   using the `command_elab` attribute.
3. All of these `CommandElab` are then tried in order until one of them does not throw an
   `unsupportedSyntaxException`, Lean's way of indicating that the elaborator
   "feels responsible"
   for this specific `Syntax` construct. Note that it can still throw a regular
   error to indicate to the user that something is wrong. If no responsible
   elaborator is found, then the command elaboration is aborted with an `unexpected syntax`
   error message.

コマンドエラボレータのタイプを理解したところで、
実際のエラボレーションプロセスがどのように機能するのかを簡単に見てみましょう：
1. 現在の`Syntax`に適用できるマクロがあるかどうかを確認します。
   適用可能でエラーをスローしないマクロがある場合、結果の`Syntax`は再度コマンドとして再帰的にエラボレートされます。
2. マクロが適用できない場合、エラボレートしている`Syntax`の`SyntaxKind`に登録されているすべての`CommandElab`を、
    `command_elab`属性を使用して検索します。
3. これらの`CommandElab`は、次のいずれかが`unsupportedSyntaxException`をスローしないまで順番に試されます。
    これはLeanがエラボレータがこの特定の`Syntax`構築物に"責任を感じる"ことを示す方法です。
    ユーザーに何かが間違っていることを示すために、通常のエラーをスローすることはまだ可能です。
    責任を持つエラボレータが見つからない場合、コマンドエラボレーションは
    `unexpected syntax`エラーメッセージと共に中止されます。

As you can see the general idea behind the procedure is quite similar to ordinary macro expansion.

この手順の背後にある一般的なアイデアは、通常のマクロ展開と非常に似ていることがわかります。

### Making our own
Now that we know both what a `CommandElab` is and how they are used, we can
start looking into writing our own. The steps for this, as we learned above, are:
1. Declaring the syntax
2. Declaring the elaborator
3. Registering the elaborator as responsible for the syntax via the `command_elab`
   attribute.

`CommandElab`が何であるか、そしてそれがどのように使用されるのかを理解したので、
自分自身のものを書き始めることができます。
上記で学んだように、これには次のステップがあります。
1. 構文の宣言
2. エラボレータの宣言
3. `command_elab`属性を介して構文に対してエラボレータを責任を持つように登録する。

Let's see how this is done:

どのようにしてこれが行われるかを見てみましょう。
-/

import Lean

open Lean Elab Command Term Meta

syntax (name := mycommand1) "#mycommand1" : command -- declare the syntax

@[command_elab mycommand1]
def mycommand1Impl : CommandElab := fun stx => do -- declare and register the elaborator
  logInfo "Hello World"

#mycommand1 -- Hello World

/-!
You might think that this is a little boiler-platey and it turns out the Lean
devs did as well so they added a macro for this!

これは少し冗長に見えるかもしれませんが、実はLeanの開発者もそう思ったので、このためのマクロを追加しました！
-/
elab "#mycommand2" : command =>
  logInfo "Hello World"

#mycommand2 -- Hello World

/-!
Note that, due to the fact that command elaboration supports multiple
registered elaborators for the same syntax, we can in fact overload
syntax, if we want to.

コマンドの詳細化が同じ構文の複数の詳細化機能をサポートしているため、
実際には構文をオーバーロードすることができます。
-/
@[command_elab mycommand1]
def myNewImpl : CommandElab := fun stx => do
  logInfo "new!"

#mycommand1 -- new!

/-!
Furthermore it is also possible to only overload parts of syntax by
throwing an `unsupportedSyntaxException` in the cases we want the default
handler to deal with it or just letting the `elab` command handle it.

さらに、`unsupportedSyntaxException`を投げることで構文の一部だけをオーバーロードすることも可能です。
これは、デフォルトのハンドラに処理させたい場合や、`elab`コマンドで処理させたい場合に使用します。

-/

/-
In the following example, we are not extending the original `#check` syntax,
but adding a new `SyntaxKind` for this specific syntax construct.
However, from the point of view of the user, the effect is basically the same.

次の例では、元の`#check`構文を拡張していませんが、
この特定の構文構築物に対して新しい`SyntaxKind`を追加しています。
しかし、ユーザーの観点からは、効果は基本的に同じです。
-/
elab "#check" "mycheck" : command => do
  logInfo "Got ya!"

/-
This is actually extending the original `#check`
-/
@[command_elab Lean.Parser.Command.check] def mySpecialCheck : CommandElab := fun stx => do
  if let some str := stx[1].isStrLit? then
    logInfo s!"Specially elaborated string literal!: {str} : String"
  else
    throwUnsupportedSyntax

#check mycheck -- Got ya!
#check "Hello" -- Specially elaborated string literal!: Hello : String
#check Nat.add -- Nat.add : Nat → Nat → Nat

/-!
### Mini project
As a final mini project for this section let's build a command elaborator
that is actually useful. It will take a command and use the same mechanisms
as `elabCommand` (the entry point for command elaboration) to tell us
which macros or elaborators are relevant to the command we gave it.

このセクションの最後の小プロジェクトとして、実際に役立つコマンドエラボレータを構築しましょう。
このエラボレータは、コマンドを取得し、`elabCommand`（コマンドエラボレーションのエントリーポイント）
と同じメカニズムを使用して、私たちが与えたコマンドに関連するマクロやエラボレータが何であるかを教えてくれます。

We will not go through the effort of actually reimplementing `elabCommand` though

実際に`elabCommand`を再実装する努力はしないでしょう。
-/
elab "#findCElab " c:command : command => do
  let macroRes ← liftMacroM <| expandMacroImpl? (←getEnv) c
  match macroRes with
  | some (name, _) => logInfo s!"Next step is a macro: {name.toString}"
  | none =>
    let kind := c.raw.getKind
    let elabs := commandElabAttribute.getEntries (←getEnv) kind
    match elabs with
    | [] => logInfo s!"There is no elaborators for your syntax, looks like its bad :("
    | _ => logInfo s!"Your syntax may be elaborated by: {elabs.map (fun el => el.declName.toString)}"

#findCElab def lala := 12 -- Your syntax may be elaborated by: [Lean.Elab.Command.elabDeclaration]
#findCElab abbrev lolo := 12 -- Your syntax may be elaborated by: [Lean.Elab.Command.elabDeclaration]
#findCElab #check foo -- even our own syntax!: Your syntax may be elaborated by: [mySpecialCheck, Lean.Elab.Command.elabCheck]
#findCElab open Hi -- Your syntax may be elaborated by: [Lean.Elab.Command.elabOpen]
#findCElab namespace Foo -- Your syntax may be elaborated by: [Lean.Elab.Command.elabNamespace]
#findCElab #findCElab open Bar -- even itself!: Your syntax may be elaborated by: [«_aux_lean_elaboration___elabRules_command#findCElab__1»]

/-!
TODO: Maybe we should also add a mini project that demonstrates a
non # style command aka a declaration, although nothing comes to mind right now.
TODO:  Define a `conjecture` declaration, similar to `lemma/theorem`, except that
it is automatically sorried.  The `sorry` could be a custom one, to reflect that
the "conjecture" might be expected to be true.

TODO: 多分、宣言としての非#スタイルのコマンドを示すミニプロジェクトも追加すべきですが、
今のところ具体的なアイディアは思いつきません。
TODO: `lemma/theorem`に似ているが、自動的に`sorry`が適用される`conjecture`宣言を定義してください。
この`sorry`はカスタムものであることができ、"conjecture"が真であることが期待されることを反映しています。
-/

/-!
## Term elaboration
A term is a `Syntax` object that represents some sort of `Expr`.
Term elaborators are the ones that do the work for most of the code we write.
Most notably they elaborate all the values of things like definitions,
types (since these are also just `Expr`) etc.

項はある種の`Expr`を表す`Syntax`オブジェクトです。
項の構築器は、私たちが書くコードの大部分の作業を行います。
特に、定義や型（これらもただの`Expr`であるため）などの値をすべて詳細に処理します。

All terms live in the `term` syntax category (which we have seen in action
in the macro chapter already). So, in order to declare custom terms, their
syntax needs to be registered in that category.

すべての項は`term`構文カテゴリに存在します（マクロの章で既に動作を見ています）。したがって、
カスタム項を宣言するには、その構文をそのカテゴリに登録する必要があります。

### Giving meaning to terms
As with command elaboration, the next step is giving some semantics to the syntax.
With terms, this is done by registering a so called term elaborator.

コマンドの詳細化と同様に、次のステップは構文にいくつかの意味を与えることです。
項については、いわゆる項の詳細化機能を登録することでこれが行われます。

Term elaborators have type `TermElab` which is an alias for:
`Syntax → Option Expr → TermElabM Expr`. This type is already
quite different from command elaboration:

項の詳細化機能は、`Syntax → Option Expr → TermElabM Expr`のエイリアスである`TermElab`の型を持ちます。
この型は、コマンドの詳細化とはかなり異なっています。

- As with command elaboration the `Syntax` is whatever the user used
  to create this term
- The `Option Expr` is the expected type of the term, since this cannot
  always be known it is only an `Option` argument
- Unlike command elaboration, term elaboration is not only executed
  because of its side effects -- the `TermElabM Expr` return value does
  actually contain something of interest, namely, the `Expr` that represents
  the `Syntax` object.

- コマンドの詳細化と同様に、`Syntax`はユーザーがこの項を作成するために使用したものです。
- `Option Expr`は項の期待される型であり、これは常にはわからないため、`Option`引数のみです。
- コマンドの詳細化とは異なり、項の詳細化は副作用のためだけに実行されるわけではありません。
  `TermElabM Expr`の返り値には、実際には興味深いものが含まれています。
  つまり、`Syntax`オブジェクトを表す`Expr`です。

`TermElabM` is basically an upgrade of `CommandElabM` in every regard:
it supports all the capabilities we mentioned above, plus two more.
The first one is quite simple: On top of running `IO` code it is also
capable of running `MetaM` code, so `Expr`s can be constructed nicely.
The second one is very specific to the term elaboration loop.

`TermElabM`は、あらゆる点で`CommandElabM`のアップグレード版と言えます：
先ほど述べたすべての機能に加えて、さらに2つの機能がサポートされています。
最初の1つは非常にシンプルです：`IO`コードの実行に加えて、`MetaM`コードも実行できるので、
`Expr`をきれいに構築することができます。
2つ目は、項の詳細化ループに特有のものです。

### Term elaboration
The basic idea of term elaboration is the same as command elaboration:
expand macros and recurse or run term elaborators that have been registered
for the `Syntax` via the `term_elab` attribute (they might in turn run term elaboration)
until we are done. There is, however, one special action that a term elaborator
can do during its execution.

項の詳細化の基本的な考え方は、コマンドの詳細化と同じです：
マクロを展開し、`term_elab`属性を通じて`Syntax`に登録された項の詳細化関数を実行または再帰的に呼び出し
（それらは項の詳細化を実行するかもしれません）完了するまで続けます。
ただし、項の詳細化関数が実行中に行うことができる特別なアクションが1つあります。

A term elaborator may throw `Except.postpone`. This indicates that
the term elaborator requires more
information to continue its work. In order to represent this missing information,
Lean uses so called synthetic metavariables. As you know from before, metavariables
are holes in `Expr`s that are waiting to be filled in. Synthetic metavariables are
different in that they have special methods that are used to solve them,
registered in `SyntheticMVarKind`. Right now, there are four of these:

項の詳細化関数は`Except.postpone`をスローすることができます。
これは、項の詳細化関数が作業を続行するためのより多くの情報を必要としていることを示しています。
この欠けている情報を表すために、Leanはいわゆる合成メタ変数を使用します。
前述の通り、メタ変数は埋められるのを待っている`Expr`の穴です。
合成メタ変数は、それらを解決するために使用される特別な方法が`SyntheticMVarKind`に登録されている
という点で異なっています。現在、これらの方法は以下の4つあります：

- `typeClass`, the metavariable should be solved with typeclass synthesis
- `coe`, the metavariable should be solved via coercion (a special case of typeclass)
- `tactic`, the metavariable is a tactic term that should be solved by running a tactic
- `postponed`, the ones that are created at `Except.postpone`

- `typeClass`：メタ変数はタイプクラス合成で解決されるべきです。
- `coe`：メタ変数は、型クラスの特別なケースである強制によって解決されるべきです。
- `tactic`：メタ変数は、タクティクを実行することで解決されるべきタクティク項です。
- `postponed`：`Except.postpone`で作成されるもの

Once such a synthetic metavariable is created, the next higher level term elaborator will continue.
At some point, execution of postponed metavariables will be resumed by the term elaborator,
in hopes that it can now complete its execution. We can try to see this in
action with the following example:

このような合成メタ変数が作成されると、次の上位レベルの項の詳細化関数が続行されます。
ある時点で、項の詳細化関数によって延期されたメタ変数の実行が再開されます。
これにより、実行が完了する可能性があるためです。
次の例でこれを実行してみましょう。
-/
#check set_option trace.Elab.postpone true in List.foldr .add 0 [1,2,3] -- [Elab.postpone] .add : ?m.5695 → ?m.5696 → ?m.5696

/-!
What happened here is that the elaborator for function applications started
at `List.foldr` which is a generic function so it created metavariables
for the implicit type parameters. Then, it attempted to elaborate the first argument `.add`.

ここで起こったことは、関数適用の詳細化関数が`List.foldr`から始まったことです。
これは一般的な関数なので、暗黙の型パラメータのためのメタ変数を作成しました。
その後、最初の引数である`.add`の詳細化を試みました。

In case you don't know how `.name` works, the basic idea is that quite
often (like in this case) Lean should be able to infer the output type (in this case `Nat`)
of a function (in this case `Nat.add`).  In such cases, the `.name` feature will then simply
search for a function named `name` in the namespace `Nat`. This is especially
useful when you want to use constructors of a type without referring to its
namespace or opening it, but can also be used like above.

`.name`の動作方法がわからない場合、基本的な考え方は、非常に頻繁に（この場合のように）
Leanは関数（この場合は`Nat.add`）の出力タイプ（この場合は`Nat`）を推論できるはずだということです。
そのような場合、`.name`機能は単に`Nat`の名前空間内で`name`という名前の関数を検索します。
これは、名前空間を参照することなく、
またはそれを開かずにタイプのコンストラクタを使用したい場合に特に役立ちますが、
上記のようにも使用できます。

Now back to our example, while Lean does at this point already know that `.add`
needs to have type: `?m1 → ?m2 → ?m2` (where `?x` is notation for a metavariable)
the elaborator for `.add` does need to know the actual value of `?m2` so the
term elaborator postpones execution (by internally creating a synthetic metavariable
in place of `.add`), the elaboration of the other two arguments then yields the fact that
`?m2` has to be `Nat` so once the `.add` elaborator is continued it can work with
this information to complete elaboration.

例に戻りますが、この時点でLeanはすでに`.add`が`?m1 → ?m2 → ?m2`という型を持つ必要があることを知っています
（ここで`?x`はメタ変数のための記法）。
しかし、`.add`の詳細化関数は`?m2`の実際の値を知る必要がありますので、項の詳細化関数は実行を先送りします
（内部的には`.add`の代わりに合成メタ変数を作成することで）。
他の2つの引数の詳細化により、`?m2`は`Nat`でなければならないという事実が得られるので、
`.add`の詳細化関数が再開されると、この情報を使用して詳細化を完了させることができます。

We can also easily provoke cases where this does not work out. For example:

これがうまくいかない場合も簡単に引き起こすことができます。例えば：
-/

#check set_option trace.Elab.postpone true in List.foldr .add
-- [Elab.postpone] .add : ?m.5808 → ?m.5809 → ?m.5809
-- invalid dotted identifier notation, expected type is not of the form (... → C ...) where C is a constant
  -- ?m.5808 → ?m.5809 → ?m.5809

/-!
In this case `.add` first postponed its execution, then got called again
but didn't have enough information to finish elaboration and thus failed.

この場合、`.add`はまず実行を先送りしましたが、再度呼び出されましたが、
詳細化を完了するのに十分な情報がなく、そのため失敗しました。

### Making our own
Adding new term elaborators works basically the same way as adding new
command elaborators so we'll only take a very brief look:

新しい項の詳細化関数を追加する方法は、基本的にコマンドの詳細化関数を追加する方法と同じなので、
非常に簡単に見てみましょう。
-/

syntax (name := myterm1) "myterm 1" : term

def mytermValues := [1, 2]

@[term_elab myterm1]
def myTerm1Impl : TermElab := fun stx type? =>
  mkAppM ``List.get! #[.const ``mytermValues [], mkNatLit 0] -- `MetaM` code

#eval myterm 1 -- 1

-- Also works with `elab`
elab "myterm 2" : term => do
  mkAppM ``List.get! #[.const ``mytermValues [], mkNatLit 1] -- `MetaM` code

#eval myterm 2 -- 2

/-!
### Mini project
As a final mini project for this chapter we will recreate one of the most
commonly used Lean syntax sugars, the `⟨a,b,c⟩` notation as a short hand
for single constructor types:

この章の最後のミニプロジェクトとして、最も一般的に使用されるLeanの構文シュガー、
単一コンストラクタ型のための短縮形である`⟨a,b,c⟩`表記を再現します。
-/

-- slightly different notation so no ambiguity happens
syntax (name := myanon) "⟨⟨" term,* "⟩⟩" : term

def getCtors (typ : Name) : MetaM (List Name) := do
  let env ← getEnv
  match env.find? typ with
  | some (ConstantInfo.inductInfo val) =>
    pure val.ctors
  | _ => pure []

@[term_elab myanon]
def myanonImpl : TermElab := fun stx typ? => do
  -- Attempt to postpone execution if the type is not known or is a metavariable.
  -- Metavariables are used by things like the function elaborator to fill
  -- out the values of implicit parameters when they haven't gained enough
  -- information to figure them out yet.
  -- Term elaborators can only postpone execution once, so the elaborator
  -- doesn't end up in an infinite loop. Hence, we only try to postpone it,
  -- otherwise we may cause an error.
  tryPostponeIfNoneOrMVar typ?
  -- If we haven't found the type after postponing just error
  let some typ := typ? | throwError "expected type must be known"
  if typ.isMVar then
    throwError "expected type must be known"
  let Expr.const base .. := typ.getAppFn | throwError s!"type is not of the expected form: {typ}"
  let [ctor] ← getCtors base | throwError "type doesn't have exactly one constructor"
  let args := TSyntaxArray.mk stx[1].getSepArgs
  let stx ← `($(mkIdent ctor) $args*) -- syntax quotations
  elabTerm stx typ -- call term elaboration recursively

#check (⟨⟨1, sorry⟩⟩ : Fin 12) -- { val := 1, isLt := (_ : 1 < 12) } : Fin 12
#check ⟨⟨1, sorry⟩⟩ -- expected type must be known
#check (⟨⟨0⟩⟩ : Nat) -- type doesn't have exactly one constructor
#check (⟨⟨⟩⟩ : Nat → Nat) -- type is not of the expected form: Nat -> Nat

/-!
As a final note, we can shorten the postponing act by using an additional
syntax sugar of the `elab` syntax instead:

最後に、`elab`構文の追加の構文シュガーを使用して、先送りの行為を短縮することができます：
-/

-- This `t` syntax will effectively perform the first two lines of `myanonImpl`
elab "⟨⟨" args:term,* "⟩⟩" : term <= t => do
  sorry


/-!

## Exercises

1. Consider the following code. Rewrite `syntax` + `@[term_elab hi]... : TermElab` combination using just `elab`.

    ```lean
    syntax (name := hi) term " ♥ " " ♥ "? " ♥ "? : term

    @[term_elab hi]
    def heartElab : TermElab := fun stx tp =>
      match stx with
        | `($l:term ♥) => do
          let nExpr ← elabTermEnsuringType l (mkConst `Nat)
          return Expr.app (Expr.app (Expr.const `Nat.add []) nExpr) (mkNatLit 1)
        | `($l:term ♥♥) => do
          let nExpr ← elabTermEnsuringType l (mkConst `Nat)
          return Expr.app (Expr.app (Expr.const `Nat.add []) nExpr) (mkNatLit 2)
        | `($l:term ♥♥♥) => do
          let nExpr ← elabTermEnsuringType l (mkConst `Nat)
          return Expr.app (Expr.app (Expr.const `Nat.add []) nExpr) (mkNatLit 3)
        | _ =>
          throwUnsupportedSyntax
    ```

-- -/

-- syntax (name := hi) term " ♥ " " ♥ "? " ♥ "? : term

-- @[term_elab hi]
-- def heartElab : TermElab := fun stx tp =>
--   match stx with
--     | `($l:term ♥) => do
--       let nExpr ← elabTermEnsuringType l (mkConst `Nat)
--       return Expr.app (Expr.app (Expr.const `Nat.add []) nExpr) (mkNatLit 1)
--     | `($l:term ♥♥) => do
--       let nExpr ← elabTermEnsuringType l (mkConst `Nat)
--       return Expr.app (Expr.app (Expr.const `Nat.add []) nExpr) (mkNatLit 2)
--     | `($l:term ♥♥♥) => do
--       let nExpr ← elabTermEnsuringType l (mkConst `Nat)
--       return Expr.app (Expr.app (Expr.const `Nat.add []) nExpr) (mkNatLit 3)
--     | _ =>
--       throwUnsupportedSyntax

-- #eval 7 ♥ -- 8
-- #eval 7 ♥♥ -- 9
-- #eval 7 ♥♥♥ -- 10


elab n:term "♥" a:"♥"? b:"♥"? : term => do
  let nExpr : Expr ← elabTermEnsuringType n (mkConst `Nat)
  if let some a := a then
    if let some b := b then
      return Expr.app (Expr.app (Expr.const `Nat.add []) nExpr) (mkNatLit 3)
    else
      return Expr.app (Expr.app (Expr.const `Nat.add []) nExpr) (mkNatLit 2)
  else
    return Expr.app (Expr.app (Expr.const `Nat.add []) nExpr) (mkNatLit 1)

#eval 7 ♥  -- 8
#eval 7 ♥♥ -- 9
#eval 7 ♥♥♥ -- 10

/-

2. Here is some syntax taken from a real mathlib command `alias`.

    ```
    syntax (name := our_alias) (docComment)? "our_alias " ident " ← " ident* : command
    ```

    We want `alias hi ← hello yes` to print out the identifiers after `←` - that is, "hello" and "yes".

    Please add these semantics:

    **a)** using `syntax` + `@[command_elab alias] def elabOurAlias : CommandElab`.
    **b)** using `syntax` + `elab_rules`.
    **c)** using `elab`.

-/
syntax (name := aliasA) (docComment)? "aliasA " ident " ← " ident* : command

@[command_elab «aliasA»]
def elabOurAliasA : CommandElab := fun stx => do
  match stx with
  | `(aliasA $x:ident ← $ys:ident*) =>
    for y in ys do
      Lean.logInfo y
  | _ =>
    throwUnsupportedSyntax

aliasA hi ← hello yes -- hello, yes


syntax (name := aliasB) (docComment)? "aliasB " ident " ← " ident* : command
elab_rules : command
  | `(command | aliasB $m:ident ← $ys:ident*) =>
    for y in ys do
      Lean.logInfo y

aliasB hello ← world yes -- world, yes

elab "aliasC " m:ident " ← " ys:ident* : command => do
  for y in ys do
    Lean.logInfo y

aliasC hello ← world yes -- world, yes
/-
3. Here is some syntax taken from a real mathlib tactic `nth_rewrite`.

    ```lean
    open Parser.Tactic
    syntax (name := nthRewriteSeq) "nth_rewrite " (config)? num rwRuleSeq (ppSpace location)? : tactic
    ```

    We want `nth_rewrite 5 [←add_zero a] at h` to print out `"rewrite location!"` if the user provided location, and `"rewrite target!"` if the user didn't provide location.

    Please add these semantics:

    **a)** using `syntax` + `@[tactic nthRewrite] def elabNthRewrite : Lean.Elab.Tactic.Tactic`.
    **b)** using `syntax` + `elab_rules`.
    **c)** using `elab`.

-/

open Parser.Tactic

syntax (name := nthRewriteA) "nth_rewriteA " (config)? num rwRuleSeq (ppSpace location)? : tactic

@[tactic nthRewriteA]
def elabNthRewriteA : Lean.Elab.Tactic.Tactic := fun stx => do
  match stx with
  | `(tactic| nth_rewriteA $[$cfg]? $n $rules $_loc) =>
    Lean.logInfo "rewrite location!"
  | `(tactic| nth_rewriteA $[$cfg]? $n $rules) =>
    Lean.logInfo "rewrite target!"
  | _ =>
    throwUnsupportedSyntax

example : 2 + 2 = 4 := by
  nth_rewriteA 2 [← add_zero] at h
  nth_rewriteA 2 [← add_zero]
  sorry

syntax (name := nthRewriteB) "nth_rewriteB " (config)? num rwRuleSeq (ppSpace location)? : tactic

elab_rules (kind := nthRewriteB) : tactic
  | `(tactic| nth_rewriteB $[$cfg]? $n $rules $_loc) =>
    Lean.logInfo "rewrite location!"
  | `(tactic| nth_rewriteB $[$cfg]? $n $rules) =>
    Lean.logInfo "rewrite target!"

example : 2 + 2 = 4 := by
  nth_rewriteB 2 [← add_zero] at h
  nth_rewriteB 2 [← add_zero]
  sorry

elab "nth_rewriteC " (config)? num rwRuleSeq loc:(ppSpace location)? : tactic =>
  if let some loc := loc then
    Lean.logInfo "rewrite location!"
  else
    Lean.logInfo "rewrite target!"

example : 2 + 2 = 4 := by
  nth_rewriteC 2 [← add_zero] at h
  nth_rewriteC 2 [← add_zero]
  sorry
