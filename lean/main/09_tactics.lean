/-
# Tactics

Tactics are Lean programs that manipulate a custom state. All tactics are, in
the end, of type `TacticM Unit`. This has the type:

タクティクスはカスタムステートを操作するLeanプログラムです。
結局のところ、すべてのタクティクスは`TacticM Unit`型です。
この型は次のとおりです：

```lean
-- from Lean/Elab/Tactic/Basic.lean
TacticM = ReaderT Context $ StateRefT State TermElabM
```

But before demonstrating how to use `TacticM`, we shall explore macro-based
tactics.

マクロベースのタクティクスの使用方法を示す前に、
マクロベースのタクティクスを探求します。

## Tactics by Macro Expansion

Just like many other parts of the Lean 4 infrastructure, tactics too can be
declared by lightweight macro expansion.

Lean 4のインフラストラクチャの多くの部分と同様に、
タクティクスも軽量なマクロ展開によって宣言することができます。

For example, we build an example of a `custom_sorry_macro` that elaborates into
a `sorry`. We write this as a macro expansion, which expands the piece of syntax
`custom_sorry_macro` into the piece of syntax `sorry`:

例として、`sorry`に展開される`custom_sorry_macro`の例を構築します。
このマクロは、構文`custom_sorry_macro`を構文`sorry`に展開する
マクロ展開として記述します。
-/

import Lean.Elab.Tactic

macro "custom_sorry_macro" : tactic => `(tactic| sorry)

example : 1 = 42 := by
  custom_sorry_macro

/-
### Implementing `trivial`: Extensible Tactics by Macro Expansion

As more complex examples, we can write a tactic such as `custom_tactic`, which
is initially completely unimplemented, and can be extended with more tactics.
We start by simply declaring the tactic with no implementation:

より複雑な例として、当初は完全に未実装で、
より多くの戦術を持つように拡張できる戦術`custom_tactic`を書くことができます。
まずは実装なしで戦術を単に宣言します：
-/

syntax "custom_tactic" : tactic

example : 42 = 42 := by
  custom_tactic
-- tactic 'tacticCustom_tactic' has not been implemented
  sorry

/-
We will now add the `rfl` tactic into `custom_tactic`, which will allow us to
prove the previous theorem

これで、`custom_tactic`に`rfl`戦術を追加し、
先の定理を証明することができるようになります。
-/

macro_rules
| `(tactic| custom_tactic) => `(tactic| rfl)

example : 42 = 42 := by
   custom_tactic
-- Goals accomplished 🎉

/-
We can now try a harder problem, that cannot be immediately dispatched by `rfl`:

今度は、`rfl`ですぐに解決できないもっと難しい問題に挑戦してみましょう。
-/

example : 43 = 43 ∧ 42 = 42:= by
  custom_tactic
-- tactic 'rfl' failed, equality expected
--   43 = 43 ∧ 42 = 42
-- ⊢ 43 = 43 ∧ 42 = 42

/-
We extend the `custom_tactic` tactic with a tactic that tries to break `And`
down with `apply And.intro`, and then (recursively (!)) applies `custom_tactic`
to the two cases with `(<;> trivial)` to solve the generated subcases `43 = 43`,
`42 = 42`.

`custom_tactic`タクティックを拡張して、
`And`を`apply And.intro`で分解しようとするタクティックを追加し、
生成されたサブケース`43 = 43`、`42 = 42`を解決するために、
`(<;> trivial)`を使って(再帰的に (!)) `custom_tactic`を2つのケースに適用します。
-/

macro_rules
| `(tactic| custom_tactic) => `(tactic| apply And.intro <;> custom_tactic)

/-
The above declaration uses `<;>` which is a *tactic combinator*. Here, `a <;> b`
means "run tactic `a`, and apply "b" to each goal produced by `a`". Thus,
`And.intro <;> custom_tactic` means "run `And.intro`, and then run
`custom_tactic` on each goal". We test it out on our previous theorem and see
that we dispatch the theorem.

上記の宣言では`<;>`という*タクティックコンビネータ*を使用しています。
ここでの`a <;> b`は「タクティック`a`を実行し、
`a`によって生成された各目標に対して`b`を適用する」という意味です。
したがって、`And.intro <;> custom_tactic`は
「`And.intro`を実行し、その後で各目標に`custom_tactic`を実行する」
という意味です。前の定理に対してテストを行い、定理を解決できることを確認します。
-/

example : 43 = 43 ∧ 42 = 42 := by
  custom_tactic
-- Goals accomplished 🎉

/-
In summary, we declared an extensible tactic called `custom_tactic`. It
initially had no elaboration at all. We added the `rfl` as an elaboration of
`custom_tactic`, which allowed it to solve the goal `42 = 42`. We then tried a
harder theorem, `43 = 43 ∧ 42 = 42` which `custom_tactic` was unable to solve.
We were then able to enrich `custom_tactic` to split "and" with `And.intro`, and
also *recursively* call `custom_tactic` in the two subcases.

まとめると、`custom_tactic`という拡張可能なタクティックを宣言しました。
初めは全く展開がありませんでした。
`rfl`を`custom_tactic`の展開として追加することで、
目標`42 = 42`を解決することができるようになりました。
次に、`custom_tactic`では解決できなかったより難しい定理
`43 = 43 ∧ 42 = 42`を試みました。
その後、`And.intro`を使って「かつ」を分割し、
2つのサブケースで*再帰的に*`custom_tactic`を呼び出すことで
`custom_tactic`を豊かにすることができました。

### Implementing `<;>`: Tactic Combinators by Macro Expansion

Recall that in the previous section, we said that `a <;> b` meant "run `a`, and
then run `b` for all goals". In fact, `<;>` itself is a tactic macro. In this
section, we will implement the syntax `a and_then b` which will stand for
"run `a`, and then run `b` for all goals".

前のセクションで述べたように、`a <;> b`とは
「`a`を実行し、その後全てのゴールに対して`b`を実行する」という意味でした。
実は、`<;>`自体もタクティックマクロです。
このセクションでは、「`a`を実行し、その後全てのゴールに対して`b`を実行する」
という意味の`a and_then b`という構文を実装します。
-/

-- 1. We declare the syntax `and_then`
-- 1. `and_then`という構文を宣言します。

syntax tactic " and_then " tactic : tactic

-- 2. We write the expander that expands the tactic
--    into running `a`, and then running `b` on all goals produced by `a`.

-- 2. タクティックを実行し、`a`によって生成されたすべてのゴールに対して
--    `b`を実行するようにタクティックを展開する展開器を書きます。

macro_rules
| `(tactic| $a:tactic and_then $b:tactic) =>
    `(tactic| $a:tactic; all_goals $b:tactic)

-- 3. We test this tactic.
-- 3. このタクティックをテストします。

theorem test_and_then: 1 = 1 ∧ 2 = 2 := by
  apply And.intro and_then rfl

#print test_and_then
-- theorem test_and_then : 1 = 1 ∧ 2 = 2 :=
-- { left := Eq.refl 1, right := Eq.refl 2 }

/-
## Exploring `TacticM`

### The simplest tactic: `sorry`

In this section, we wish to write a tactic that fills the proof with sorry:

このセクションでは、証明を`sorry`で埋めるタクティックを書きます。

```lean
example : 1 = 2 := by
  custom_sorry
```

We begin by declaring such a tactic:

このようなタクティックを宣言することから始めます。
-/

elab "custom_sorry_0" : tactic => do
  return

example : 1 = 2 := by
  custom_sorry_0
-- unsolved goals: ⊢ 1 = 2

/-
This defines a syntax extension to Lean, where we are naming the piece of syntax
`custom_sorry_0` as living in `tactic` syntax category. This informs the
elaborator that, in the context of elaborating `tactic`s, the piece of syntax
`custom_sorry_0` must be elaborated as what we write to the right-hand-side of
the `=>` (the actual implementation of the tactic).

これはLeanに対する構文拡張を定義しており、
`tactic`構文カテゴリに属する`custom_sorry_0`という構文を命名しています。
これにより、`tactic`を展開するコンテキストにおいて、
`custom_sorry_0`という構文は`=>`の右側に書かれたもの
（タクティックの実際の実装）として展開されなければならないことを
エラボレーターに通知します。

Next, we write a term in `TacticM Unit` to fill in the goal with `sorryAx α`,
which can synthesize an artificial term of type `α`. To do this, we first access
the goal with `Lean.Elab.Tactic.getMainGoal : Tactic MVarId`, which returns the
main goal, represented as a metavariable. Recall that under
types-as-propositions, the type of our goal must be the proposition that `1 = 2`.
We check this by printing the type of `goal`.

次に、`TacticM Unit`で`sorryAx α`を使って目標を埋める項を書きます。
これは型`α`の人工的な項を生成することができます。
これを行うために、`Lean.Elab.Tactic.getMainGoal : Tactic MVarId`を使って
目標にアクセスします。これはメタ変数として表されるメインゴールを返します。
型としての命題の下で、私たちの目標の型は`1 = 2`である命題でなければならないことを
覚えておいてください。`goal`の型を印刷することでこれを確認します。

But first we need to start our tactic with `Lean.Elab.Tactic.withMainContext`,
which computes in `TacticM` with an updated context.

しかしまず、更新されたコンテキストで`TacticM`を計算するために、
`Lean.Elab.Tactic.withMainContext`でタクティクを開始する必要があります。
-/

elab "custom_sorry_1" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalDecl ← goal.getDecl
    let goalType := goalDecl.type
    dbg_trace f!"goal type: {goalType}"

example : 1 = 2 := by
  custom_sorry_1
-- goal type: Eq.{1} Nat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
-- unsolved goals: ⊢ 1 = 2

/-
To `sorry` the goal, we can use the helper `Lean.Elab.admitGoal`:

ゴールを`sorry`で埋めるためには、
ヘルパー関数`Lean.Elab.admitGoal`を使用することができます。
-/

elab "custom_sorry_2" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    Lean.Elab.admitGoal goal

theorem test_custom_sorry : 1 = 2 := by
  custom_sorry_2

#print test_custom_sorry
-- theorem test_custom_sorry : 1 = 2 :=
-- sorryAx (1 = 2) true

/-
And we no longer have the error `unsolved goals: ⊢ 1 = 2`.

そして、もはや `unsolved goals: ⊢ 1 = 2` というエラーは出ていません。

### The `custom_assump` tactic: Accessing Hypotheses

In this section, we will learn how to access the hypotheses to prove a goal. In
particular, we shall attempt to implement a tactic `custom_assump`, which looks
for an exact match of the goal among the hypotheses, and solves the theorem if
possible.

このセクションでは、目標を証明するために仮定にアクセスする方法を学びます。
特に、`custom_assump` というタクティックを実装しようと試みます。
このタクティックは、仮定の中で目標と完全に一致するものを探し、
可能であれば定理を解決します。

In the example below, we expect `custom_assump` to use `(H2 : 2 = 2)` to solve
the goal `(2 = 2)`:

以下の例では、`custom_assump`が`(H2 : 2 = 2)`を使用して
目標`(2 = 2)`を解決することを期待します。

```lean
theorem assump_correct (H1 : 1 = 1) (H2 : 2 = 2) : 2 = 2 := by
  custom_assump

#print assump_correct
-- theorem assump_correct : 1 = 1 → 2 = 2 → 2 = 2 :=
-- fun H1 H2 => H2
```

When we do not have a matching hypothesis to the goal, we expect the tactic
`custom_assump` to throw an error, telling us that we cannot find a hypothesis
of the type we are looking for:

目標に合致する仮説がない場合、`custom_assump`がエラーを投げて、
私たちが探しているタイプの仮説を見つけることができないと伝えることを期待します。

```lean
theorem assump_wrong (H1 : 1 = 1) : 2 = 2 := by
  custom_assump

#print assump_wrong
-- tactic 'custom_assump' failed, unable to find matching hypothesis of type (2 = 2)
-- H1 : 1 = 1
-- ⊢ 2 = 2
```

We begin by accessing the goal and the type of the goal so we know what we
are trying to prove. The `goal` variable will soon be used to help us create
error messages.

目標と目標のタイプにアクセスして、何を証明しようとしているのかを知ります。
「goal」変数はすぐに、エラーメッセージの作成に役立てるために使用されます。
-/

elab "custom_assump_0" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goalType ← Lean.Elab.Tactic.getMainTarget
    dbg_trace f!"goal type: {goalType}"

example (H1 : 1 = 1) (H2 : 2 = 2): 2 = 2 := by
  custom_assump_0
-- goal type: Eq.{1} Nat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
-- unsolved goals
-- H1 : 1 = 1
-- H2 : 2 = 2
-- ⊢ 2 = 2

example (H1 : 1 = 1): 2 = 2 := by
  custom_assump_0
-- goal type: Eq.{1} Nat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
-- unsolved goals
-- H1 : 1 = 1
-- ⊢ 2 = 2

/-
Next, we access the list of hypotheses, which are stored in a data structure
called `LocalContext`. This is accessed via `Lean.MonadLCtx.getLCtx`. The
`LocalContext` contains `LocalDeclaration`s, from which we can extract
information such as the name that is given to declarations (`.userName`), the
expression of the declaration (`.toExpr`). Let's write a tactic called
`list_local_decls` that prints the local declarations:

次に、`LocalContext` というデータ構造に保存されている仮定のリストにアクセスします。
これは `Lean.MonadLCtx.getLCtx` を通じてアクセスされます。
`LocalContext` には `LocalDeclaration` が含まれており、
宣言に与えられた名前（`.userName`）、
宣言の式（`.toExpr`）などの情報を抽出することができます。
ローカル宣言を印刷する `list_local_decls` というタクティックを書きましょう。
-/

elab "list_local_decls_1" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    ctx.forM fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr -- Find the expression of the declaration.
      let declName := decl.userName -- Find the name of the declaration.
      dbg_trace f!"+ local decl: name: {declName} | expr: {declExpr}"

example (H1 : 1 = 1) (H2 : 2 = 2): 1 = 1 := by
  list_local_decls_1
-- + local decl: name: test_list_local_decls_1 | expr: _uniq.3339
-- + local decl: name: H1 | expr: _uniq.3340
-- + local decl: name: H2 | expr: _uniq.3341
  rfl

/-
Recall that we are looking for a local declaration that has the same type as the
hypothesis. We get the type of `LocalDecl` by calling
`Lean.Meta.inferType` on the local declaration's expression.

仮説と同じ型を持つローカル宣言を探していることを思い出してください。
`LocalDecl`の型は、ローカル宣言の式に対して
`Lean.Meta.inferType`を呼び出すことによって取得します。
-/

elab "list_local_decls_2" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    ctx.forM fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr -- Find the expression of the declaration.
      let declName := decl.userName -- Find the name of the declaration.
      let declType ← Lean.Meta.inferType declExpr -- **NEW:** Find the type.
      dbg_trace f!"+ local decl: name: {declName} | expr: {declExpr} | type: {declType}"

example (H1 : 1 = 1) (H2 : 2 = 2): 1 = 1 := by
  list_local_decls_2
  -- + local decl: name: test_list_local_decls_2 | expr: _uniq.4263 | type: (Eq.{1} Nat ...)
  -- + local decl: name: H1 | expr: _uniq.4264 | type: Eq.{1} Nat ...)
  -- + local decl: name: H2 | expr: _uniq.4265 | type: Eq.{1} Nat ...)
  rfl

/-
We check if the type of the `LocalDecl` is equal to the goal type with
`Lean.Meta.isExprDefEq`. See that we check if the types are equal at `eq?`, and
we print that `H1` has the same type as the goal
(`local decl[EQUAL? true]: name: H1`), and we print that `H2` does not have the
same type (`local decl[EQUAL? false]: name: H2 `):

目標の型と`LocalDecl`の型が等しいかどうかは、`Lean.Meta.isExprDefEq`で確認します。
`eq?`で型が等しいかどうかをチェックし、
`H1`が目標と同じ型を持っていること（`local decl[EQUAL? true]: name: H1`）と、
`H2`が同じ型を持っていないこと（`local decl[EQUAL? false]: name: H2 `）
を印刷します。
-/

elab "list_local_decls_3" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    ctx.forM fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr -- Find the expression of the declaration.
      let declName := decl.userName -- Find the name of the declaration.
      let declType ← Lean.Meta.inferType declExpr -- Find the type.
      let eq? ← Lean.Meta.isExprDefEq declType goalType -- **NEW** Check if type equals goal type.
      dbg_trace f!"+ local decl[EQUAL? {eq?}]: name: {declName}"

example (H1 : 1 = 1) (H2 : 2 = 2): 1 = 1 := by
  list_local_decls_3
-- + local decl[EQUAL? false]: name: test_list_local_decls_3
-- + local decl[EQUAL? true]: name: H1
-- + local decl[EQUAL? false]: name: H2
  rfl

/-
Finally, we put all of these parts together to write a tactic that loops over
all declarations and finds one with the correct type. We loop over declarations
with `lctx.findDeclM?`. We infer the type of declarations with
`Lean.Meta.inferType`. We check that the declaration has the same type as the
goal with `Lean.Meta.isExprDefEq`:

最後に、これらすべての部品を組み合わせて、
正しい型を持つ宣言を見つけるタクティックを書きます。
`lctx.findDeclM?`を使って宣言をループし、
`Lean.Meta.inferType`で宣言の型を推論し、
`Lean.Meta.isExprDefEq`で宣言が目標と同じ型を持つかどうかをチェックします。
-/

elab "custom_assump_1" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let lctx ← Lean.MonadLCtx.getLCtx
    -- Iterate over the local declarations...
    let option_matching_expr ← lctx.findDeclM? fun ldecl: Lean.LocalDecl => do
      let declExpr := ldecl.toExpr -- Find the expression of the declaration.
      let declType ← Lean.Meta.inferType declExpr -- Find the type.
      if (← Lean.Meta.isExprDefEq declType goalType) -- Check if type equals goal type.
      then return some declExpr -- If equal, success!
      else return none          -- Not found.
    dbg_trace f!"matching_expr: {option_matching_expr}"

example (H1 : 1 = 1) (H2 : 2 = 2) : 2 = 2 := by
  custom_assump_1
-- matching_expr: some _uniq.6241
  rfl

example (H1 : 1 = 1) : 2 = 2 := by
  custom_assump_1
-- matching_expr: none
  rfl

/-
Now that we are able to find the matching expression, we need to close the
theorem by using the match. We do this with `Lean.Elab.Tactic.closeMainGoal`.
When we do not have a matching expression, we throw an error with
`Lean.Meta.throwTacticEx`, which allows us to report an error corresponding to a
given goal. When throwing this error, we format the error using `m!"..."` which
builds a `MessageData`. This provides nicer error messages than using `f!"..."`
which builds a `Format`. This is because `MessageData` also runs *delaboration*,
which allows it to convert raw Lean terms like
`(Eq.{1} Nat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))`
into readable strings like`(2 = 2)`. The full code listing given below shows how
to do this:

今、我々は一致する式を見つけることができるようになったので、
その一致を使って定理を閉じる必要があります。
これを`Lean.Elab.Tactic.closeMainGoal`で行います。
一致する式がない場合は、`Lean.Meta.throwTacticEx`を使ってエラーを投げます。
これにより、特定の目標に対応するエラーを報告することができます。
このエラーを投げるとき、エラーを`m!"..."`を使ってフォーマットします。
これは`MessageData`を構築します。
これは`f!"..."`を使うよりも、`Format`を構築するよりも良いエラーメッセージを提供します。
これは、`MessageData`は*delaboration*も実行するためであり、
これにより生のLeanの項
（例：`(Eq.{1} Nat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))`）
を読みやすい文字列（例：`(2 = 2)`）に変換することができます。
以下に示す完全なコードリストは、これをどのように行うかを示しています：
-/

elab "custom_assump_2" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let ctx ← Lean.MonadLCtx.getLCtx
    let option_matching_expr ← ctx.findDeclM? fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr
      let declType ← Lean.Meta.inferType declExpr
      if ← Lean.Meta.isExprDefEq declType goalType
        then return Option.some declExpr
        else return Option.none
    match option_matching_expr with
    | some e => Lean.Elab.Tactic.closeMainGoal e
    | none =>
      Lean.Meta.throwTacticEx `custom_assump_2 goal
        (m!"unable to find matching hypothesis of type ({goalType})")

example (H1 : 1 = 1) (H2 : 2 = 2) : 2 = 2 := by
  custom_assump_2

example (H1 : 1 = 1): 2 = 2 := by
  custom_assump_2
-- tactic 'custom_assump_2' failed, unable to find matching hypothesis of type (2 = 2)
-- H1 : 1 = 1
-- ⊢ 2 = 2

/-
### Tweaking the context

Until now, we've only performed read-like operations with the context. But what
if we want to change it? In this section we will see how to change the order of
goals and how to add content to it (new hypotheses).

これまで、コンテキストに対して読み取りのような操作のみを行ってきました。
しかし、それを変更したい場合はどうでしょうか？
このセクションでは、目標の順序を変更する方法と、
そこに新しい仮説を追加する方法を見ていきます。

Then, after elaborating our terms, we will need to use the helper function
`Lean.Elab.Tactic.liftMetaTactic`, which allows us to run computations in
`MetaM` while also giving us the goal `MVarId` for us to play with. In the end
of our computation, `liftMetaTactic` expects us to return a `List MVarId` as the
resulting list of goals.

用語を詳細に説明した後、補助関数 `Lean.Elab.Tactic.liftMetaTactic`
を使用する必要があります。
これにより、計算を `MetaM` で実行しつつ、
操作するための目標 `MVarId` も提供されます。
計算の最後に、`liftMetaTactic` は結果として得られる目標のリストとして
 `List MVarId` を返すことを期待します。

The only substantial difference between `custom_let` and `custom_have` is that
the former uses `Lean.MVarId.define` and the later uses `Lean.MVarId.assert`:

カスタムの `let` と `have` の間において唯一の実質的な違いは、
前者が `Lean.MVarId.define` を使用し、
後者が `Lean.MVarId.assert` を使用することです。
-/

open Lean.Elab.Tactic in
elab "custom_let " n:ident " : " t:term " := " v:term : tactic =>
  withMainContext do
    let t ← elabTerm t none
    let v ← elabTermEnsuringType v t
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.define n.getId t v
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]

open Lean.Elab.Tactic in
elab "custom_have " n:ident " : " t:term " := " v:term : tactic =>
  withMainContext do
    let t ← elabTerm t none
    let v ← elabTermEnsuringType v t
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.assert n.getId t v
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]

theorem test_faq_have : True := by
  custom_let n : Nat := 5
  custom_have h : n = n := rfl
-- n : Nat := 5
-- h : n = n
-- ⊢ True
  trivial

/-
### "Getting" and "Setting" the list of goals

To illustrate these, let's build a tactic that can reverse the list of goals.
We can use `Lean.Elab.Tactic.getGoals` and `Lean.Elab.Tactic.setGoals`:

これを説明するために、目標リストを逆にする戦術を構築してみましょう。
`Lean.Elab.Tactic.getGoals`と`Lean.Elab.Tactic.setGoals`を使用できます。
-/

elab "reverse_goals" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goals : List Lean.MVarId ← Lean.Elab.Tactic.getGoals
    Lean.Elab.Tactic.setGoals goals.reverse

theorem test_reverse_goals : (1 = 2 ∧ 3 = 4) ∧ 5 = 6 := by
  constructor
  constructor
-- case left.left
-- ⊢ 1 = 2
-- case left.right
-- ⊢ 3 = 4
-- case right
-- ⊢ 5 = 6
  reverse_goals
-- case right
-- ⊢ 5 = 6
-- case left.right
-- ⊢ 3 = 4
-- case left.left
-- ⊢ 1 = 2

/-
## FAQ

In this section, we collect common patterns that are used during writing tactics,
to make it easy to find common patterns.

このセクションでは、戦術を書く際に使われる一般的なパターンを集めて、
共通のパターンを簡単に見つけられるようにします。

**Q: How do I use goals?**

**Q: どのようにして目標を使いますか？**

A: Goals are represented as metavariables. The module `Lean.Elab.Tactic.Basic`
has many functions to add new goals, switch goals, etc.

A: 目標はメタ変数として表されます。
`Lean.Elab.Tactic.Basic` モジュールには、新しい目標を追加したり、
目標を切り替えたりするための多くの関数があります。

**Q: How do I get the main goal?**

**Q: メインゴールをどのようにして取得しますか？**

A: Use `Lean.Elab.Tactic.getMainGoal`.

A: `Lean.Elab.Tactic.getMainGoal` を使用します。
-/

elab "faq_main_goal" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    dbg_trace f!"goal: {goal.name}"

example : 1 = 1 := by
  faq_main_goal
-- goal: _uniq.9298
  rfl

/-
**Q: How do I get the list of goals?**

**Q: どのようにしてゴールのリストを取得しますか？**

A: Use `getGoals`.

A: `getGoals` を使用します。
-/

elab "faq_get_goals" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goals ← Lean.Elab.Tactic.getGoals
    goals.forM $ fun goal => do
      let goalType ← goal.getType
      dbg_trace f!"goal: {goal.name} | type: {goalType}"

example (b : Bool) : b = true := by
  cases b
  faq_get_goals
-- goal: _uniq.10067 | type: Eq.{1} Bool Bool.false Bool.true
-- goal: _uniq.10078 | type: Eq.{1} Bool Bool.true Bool.true
  sorry
  rfl

/-
**Q: How do I get the current hypotheses for a goal?**

**Q: ゴールの現在の仮定をどのようにして取得しますか？**

A: Use `Lean.MonadLCtx.getLCtx` which provides the local context, and then
iterate on the `LocalDeclaration`s of the `LocalContext` with accessors such as
`foldlM` and `forM`.

A: `Lean.MonadLCtx.getLCtx` を使用してローカルコンテキストを取得し、
`foldlM` や `forM` などのアクセッサを使って
 `LocalContext` の `LocalDeclaration` をイテレートします。
-/

elab "faq_get_hypotheses" : tactic =>
  Lean.Elab.Tactic.withMainContext do
  let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
  ctx.forM (fun (decl : Lean.LocalDecl) => do
    let declExpr := decl.toExpr -- Find the expression of the declaration.
    let declType := decl.type -- Find the type of the declaration.
    let declName := decl.userName -- Find the name of the declaration.
    dbg_trace f!" local decl: name: {declName} | expr: {declExpr} | type: {declType}"
  )

example (H1 : 1 = 1) (H2 : 2 = 2): 3 = 3 := by
  faq_get_hypotheses
  -- local decl: name: _example | expr: _uniq.10814 | type: ...
  -- local decl: name: H1 | expr: _uniq.10815 | type: ...
  -- local decl: name: H2 | expr: _uniq.10816 | type: ...
  rfl

/-
**Q: How do I evaluate a tactic?**

**Q: タクティックをどのように評価しますか？**

A: Use `Lean.Elab.Tactic.evalTactic: Syntax → TacticM Unit` which evaluates a
given tactic syntax. One can create tactic syntax using the macro
`` `(tactic| ⋯)``.

A: 与えられたタクティック構文を評価する
`Lean.Elab.Tactic.evalTactic: Syntax → TacticM Unit` を使用します。
マクロ `` `(tactic| ⋯)`` を使ってタクティック構文を作成できます。

For example, one could call `try rfl` with the piece of code:

例えば、次のコード片を使用して `try rfl` を呼び出すことができます：

```lean
Lean.Elab.Tactic.evalTactic (← `(tactic| try rfl))
```

**Q: How do I check if two expressions are equal?**

**Q: 2つの式が等しいかどうかをどのようにしてチェックしますか？**

A: Use `Lean.Meta.isExprDefEq <expr-1> <expr-2>`.

A: `Lean.Meta.isExprDefEq <expr-1> <expr-2>` を使用します。
-/

#check Lean.Meta.isExprDefEq
-- Lean.Meta.isExprDefEq : Lean.Expr → Lean.Expr → Lean.MetaM Bool

/-
**Q: How do I throw an error from a tactic?**

**Q: タクティックからエラーを投げるにはどうすればよいですか？**

A: Use `throwTacticEx <tactic-name> <goal-mvar> <error>`.

A: `throwTacticEx <tactic-name> <goal-mvar> <error>` を使用します。
-/

elab "faq_throw_error" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    Lean.Meta.throwTacticEx `faq_throw_error goal "throwing an error at the current goal"

example (b : Bool): b = true := by
  cases b;
  faq_throw_error
  -- case true
  -- ⊢ true = true
  -- tactic 'faq_throw_error' failed, throwing an error at the current goal
  -- case false
  -- ⊢ false = true

/-
~~ここまで~~
**Q: What is the difference between `Lean.Elab.Tactic.*` and `Lean.Meta.Tactic.*`?**

**Q: `Lean.Elab.Tactic.*` と `Lean.Meta.Tactic.*` の違いは何ですか？**

A: `Lean.Meta.Tactic.*` contains low level code that uses the `Meta` monad to
implement basic features such as rewriting. `Lean.Elab.Tactic.*` contains
high-level code that connects the low level development in `Lean.Meta` to the
tactic infrastructure and the parsing front-end.

A: `Lean.Meta.Tactic.*` には `Meta` モナドを使用して書き換えなどの
基本的な機能を実装する低レベルのコードが含まれています。
`Lean.Elab.Tactic.*` には、`Lean.Meta` の低レベルの開発を
タクティックのインフラストラクチャや解析フロントエンドに接続する
高レベルのコードが含まれています。

## Exercises

1. Consider the theorem `p ∧ q ↔ q ∧ p`. We could either write its proof as a proof term, or construct it using the tactics.
    When we are writing the proof of this theorem *as a proof term*, we're gradually filling up `_`s with certain expressions, step by step. Each such step corresponds to a tactic.

    考えてみましょう、定理 `p ∧ q ↔ q ∧ p` についてです。
    この定理の証明は、証明項として書くことも、戦術(tactics)を用いて構築することもできます。
    定理の証明を*証明項として*書く場合、段階的に `_` を特定の表現で埋めていきます。
    それぞれのステップは戦術に対応しています。

    There are many combinations of steps in which we could write this proof term - but consider the sequence of steps we wrote below. Please write each step as a tactic.
    The tactic `step_1` is filled in, please do the same for the remaining tactics (for the sake of the exercise, try to use lower-level apis, such as `mkFreshExprMVar`, `mvarId.assign` and `modify fun _ => { goals := ~)`.

    この証明項を書くためのステップの組み合わせは多数ありますが、
    以下に書かれているステップのシーケンスを考慮してください。各ステップを戦術として書いてください。
    戦術 `step_1` は記入されていますので、残りの戦術についても同様に行ってください
    （この練習のため、`mkFreshExprMVar`、`mvarId.assign`、`modify fun _ => { goals := ~`
    のような低レベルのAPIを使ってみてください）。

```lean
    -- [this is the initial goal]
    example : p ∧ q ↔ q ∧ p :=
      _

    -- step_1
    example : p ∧ q ↔ q ∧ p :=
      Iff.intro _ _

    -- step_2
    example : p ∧ q ↔ q ∧ p :=
      Iff.intro
        (
          fun hA =>
          _
        )
        (
          fun hB =>
          (And.intro hB.right hB.left)
        )

    -- step_3
    example : p ∧ q ↔ q ∧ p :=
      Iff.intro
        (
          fun hA =>
          (And.intro _ _)
        )
        (
          fun hB =>
          (And.intro hB.right hB.left)
        )

    -- step_4
    example : p ∧ q ↔ q ∧ p :=
      Iff.intro
        (
          fun hA =>
          (And.intro hA.right hA.left)
        )
        (
          fun hB =>
          (And.intro hB.right hB.left)
        )
    ```

    ```lean
    elab "step_1" : tactic => do
      let mvarId ← getMainGoal
      let goalType ← getMainTarget

      let Expr.app (Expr.app (Expr.const `Iff _) a) b := goalType | throwError "Goal type is not of the form `a ↔ b`"

      -- 1. Create new `_`s with appropriate types.
      let mvarId1 ← mkFreshExprMVar (Expr.forallE `xxx a b .default) (userName := "red")
      let mvarId2 ← mkFreshExprMVar (Expr.forallE `yyy b a .default) (userName := "blue")

      -- 2. Assign the main goal to the expression `Iff.intro _ _`.
      mvarId.assign (mkAppN (Expr.const `Iff.intro []) #[a, b, mvarId1, mvarId2])

      -- 3. Report the new `_`s to Lean as the new goals.
      modify fun _ => { goals := [mvarId1.mvarId!, mvarId2.mvarId!] }
    ```

    ```lean
    theorem gradual (p q : Prop) : p ∧ q ↔ q ∧ p := by
      step_1
      step_2
      step_3
      step_4
    ```

2. In the first exercise, we used lower-level `modify` api to update our goals.
    `liftMetaTactic`, `setGoals`, `appendGoals`, `replaceMainGoal`, `closeMainGoal`, etc. are all syntax sugars on top of `modify fun s : State => { s with goals := myMvarIds }`.
    Please rewrite the `forker` tactic with:

    最初の演習では、目標を更新するために低レベルの `modify` APIを使用しました。
    `liftMetaTactic`、`setGoals`、`appendGoals`、
    `replaceMainGoal`、`closeMainGoal` などはすべて、
    `modify fun s : State => { s with goals := myMvarIds }`
    の上に構築されたシンタックスシュガーです。
    次の内容を用いて `forker` 戦術を書き換えてください：

    **a)** `liftMetaTactic`
    **b)** `setGoals`
    **c)** `replaceMainGoal`

    ```lean
    elab "forker" : tactic => do
      let mvarId ← getMainGoal
      let goalType ← getMainTarget

      let (Expr.app (Expr.app (Expr.const `And _) p) q) := goalType | Lean.Meta.throwTacticEx `forker mvarId (m!"Goal is not of the form P ∧ Q")

      mvarId.withContext do
        let mvarIdP ← mkFreshExprMVar p (userName := "red")
        let mvarIdQ ← mkFreshExprMVar q (userName := "blue")

        let proofTerm := mkAppN (Expr.const `And.intro []) #[p, q, mvarIdP, mvarIdQ]
        mvarId.assign proofTerm

        modify fun state => { goals := [mvarIdP.mvarId!, mvarIdQ.mvarId!] ++ state.goals.drop 1 }
    ```

    ```lean
    example (A B C : Prop) : A → B → C → (A ∧ B) ∧ C := by
      intro hA hB hC
      forker
      forker
      assumption
      assumption
      assumption
    ```

3. In the first exercise, you created your own `intro` in `step_2` (with a hardcoded hypothesis name, but the basics are the same). When writing tactics, we usually want to use functions such as `intro`, `intro1`, `intro1P`, `introN` or `introNP`.

  2番目の演習で、`step_2`に独自の`intro`を作成しました（仮定名はハードコードされていますが、基本は同じです）。
  タクティックを書くときは、通常、`intro`、`intro1`、`intro1P`、`introN`、`introNP`などの関数を使用したいものです。

    For each of the points below, create a tactic `introductor` (one per each point), that turns the goal `(ab: a = b) → (bc: b = c) → (a = c)`:

    以下の各ポイントについて、目標`(ab: a = b) → (bc: b = c) → (a = c)`を変換する
    タクティック`introductor`を作成します（各ポイントごとに1つ）。

    **a)** into the goal `(a = c)` with hypotheses `(ab✝: a = b)` and `(bc✝: b = c)`.
    **b)** into the goal `(bc: b = c) → (a = c)` with hypothesis `(ab: a = b)`.
    **c)** into the goal `(bc: b = c) → (a = c)` with hypothesis `(hello: a = b)`.

    ```lean
    example (a b c : Nat) : (ab: a = b) → (bc: b = c) → (a = c) := by
      introductor
      sorry
    ```

    Hint: **"P"** in `intro1P` and `introNP` stands for **"Preserve"**.
-/
