/-
# Macros

## What is a macro
Macros in Lean are `Syntax → MacroM Syntax` functions. `MacroM` is the macro
monad which allows macros to have some static guarantees we will discuss in the
next section, you can mostly ignore it for now.

Leanのマクロは、`Syntax → MacroM Syntax` 関数です。
`MacroM`は、マクロにいくつかの静的な保証を持たせることを可能にするマクロモナドです。
次のセクションで詳しく説明しますが、現時点ではほとんど無視しても問題ありません。

Macros are registered as handlers for a specific syntax declaration using the
`macro` attribute. The compiler will take care of applying these function
to the syntax for us before performing actual analysis of the input. This
means that the only thing we have to do is declare our syntax with a specific
name and bind a function of type `Lean.Macro` to it. Let's try to reproduce
the `LXOR` notation from the `Syntax` chapter:

マクロは、`macro`属性を使って特定の構文宣言のハンドラとして登録されます。
コンパイラは、入力の実際の解析を行う前に、これらの関数を構文に適用することを担当します。
つまり、私たちがしなければならないことは、特定の名前で構文を宣言し、
その構文に`Lean.Macro`型の関数をバインドすることだけです。
`Syntax`章から`LXOR`構文を再現してみましょう。
-/

import Lean

open Lean

syntax:10 (name := lxor) term:10 " LXOR " term:11 : term

@[macro lxor] def lxorImpl : Macro
  | `($l:term LXOR $r:term) => `(!$l && $r) -- we can use the quotation mechanism to create `Syntax` in macros
  | _ => Macro.throwUnsupported

#eval true LXOR true -- false
#eval true LXOR false -- false
#eval false LXOR true -- true
#eval false LXOR false -- false

/-
That was quite easy! The `Macro.throwUnsupported` function can be used by a macro
to indicate that "it doesn't feel responsible for this syntax". In this case
it's merely used to fill a wildcard pattern that should never be reached anyways.

非常に簡単でしたね！`Macro.throwUnsupported`関数は、
マクロが「この構文に対して責任を感じない」と示すために使用できます。
この場合、それはどちらにせよ到達すべきではないワイルドカードパターンを埋めるために
単に使用されています。

However we can in fact register multiple macros for the same syntax this way
if we desire, they will be tried one after another (the later registered ones have 
higher priority)  -- is "higher" correct?
until one throws either a real error using `Macro.throwError` or succeeds, that
is it does not `Macro.throwUnsupported`. Let's see this in action:

しかし、実際には、同じ構文に対して複数のマクロを登録することができます。
それらは、1つずつ試されます（後で登録されたものほど優先度が高い）。
`Macro.throwError`を使用して本当のエラーをスローするか、成功するまで、
つまり`Macro.throwUnsupported`をスローしないまで。
動かしながら見てみましょう。
-/

@[macro lxor] def lxorImpl2 : Macro
  -- special case that changes behaviour of the case where the left and
  -- right hand side are these specific identifiers
  | `(true LXOR true) => `(true)
  | _ => Macro.throwUnsupported

#eval true LXOR true -- true, handled by new macro
#eval true LXOR false -- false, still handled by the old

/-
This capability is obviously *very* powerful! It should not be used
lightly and without careful thinking since it can introduce weird
behaviour while writing code later on. The following example illustrates
this weird behaviour:

この機能は明らかに*非常に*強力です！
後でコードを書くときに奇妙な振る舞いを引き起こす可能性があるため、
軽率に使用してはいけません。
次の例は、この奇妙な振る舞いを説明しています。
-/

#eval true LXOR true -- true, handled by new macro

def foo := true
#eval foo LXOR foo -- false, handled by old macro, after all the identifiers have a different name

/-
Without knowing exactly how this macro is implemented this behaviour
will be very confusing to whoever might be debugging an issue based on this.
The rule of thumb for when to use a macro vs. other mechanisms like
elaboration is that as soon as you are building real logic like in the 2nd
macro above, it should most likely not be a macro but an elaborator
(explained in the elaboration chapter). This means ideally we want to
use macros for simple syntax to syntax translations, that a human could
easily write out themselves as well but is too lazy to.

このマクロが具体的にどのように実装されているかを正確に把握しないと、
この動作はデバッグ中の問題に基づいて問題を追跡しようとしている人にとって非常に混乱することでしょう。
マクロとエラボレーションのような他のメカニズムをいつ使用すべきかの基本的な原則は、
2番目のマクロのように実際のロジックを構築し始めると、
おそらくそれはマクロではなくエラボレータ（エラボレーションの章で説明されています）
であるべきであることです。
したがって、理想的には、マクロはシンプルな構文から構文への変換に使用することを意味し、
それは人間が自分で書くことができるが、怠けてしまうようなものです。

## Simplifying macro declaration
Now that we know the basics of what a macro is and how to register it
we can take a look at slightly more automated ways to do this (in fact
all of the ways about to be presented are implemented as macros themselves).

マクロの基本的な内容とその登録方法を理解したので、これをもう少し自動化した方法を見てみることができます
（実際、以下で紹介される方法はすべて、それ自体がマクロとして実装されています）。

First things first there is `macro_rules` which basically desugars to
functions like the ones we wrote above, for example:

まず第一に、`macro_rules`があります。
これは、上記で書いたような関数にデシュガーされるものです。
例えば：
-/

syntax:10 term:10 " RXOR " term:11 : term

macro_rules
  | `($l:term RXOR $r:term) => `($l && !$r)

/-
As you can see, it figures out lot's of things on its own for us:
- the name of the syntax declaration
- the `macro` attribute registration
- the `throwUnsupported` wildcard

上記でわかるように、これは私たちのために多くのことを自動的に解決してくれます。
- 構文宣言の名前
- `macro`属性の登録
- `throwUnsupported`ワイルドカード

apart from this it just works like a function that is using pattern
matching syntax, we can in theory encode arbitrarily complex macro
functions on the right hand side.

これ以外にも、パターンマッチング構文を使用している関数のように機能します。
理論的には、右辺に任意に複雑なマクロ関数をエンコードすることができます。

If this is still not short enough for you, there is a next step using the
`macro` macro:

これでもまだ短くないと思う場合は、`macro`マクロを使用することができます。
-/

macro l:term:10 " ⊕ " r:term:11 : term => `((!$l && $r) || ($l && !$r))

#eval true ⊕ true -- false
#eval true ⊕ false -- true
#eval false ⊕ true -- true
#eval false ⊕ false -- false

/-
As you can see, `macro` is quite close to `notation` already:
- it performed syntax declaration for us
- it automatically wrote a `macro_rules` style function to match on it

上記のように、`macro`は`notation`に非常に近いです。
- 構文宣言を自動的に行ってくれる
- `macro_rules`スタイルの関数を自動的にマッチングする

The are of course differences as well:
- `notation` is limited to the `term` syntax category
- `notation` cannot have arbitrary macro code on the right hand side

もちろん、違いもあります。
- `notation`は`term`構文カテゴリに限定されています。
- `notation`は右辺に任意のマクロコードを持つことはできません。

## `Syntax` Quotations
### The basics
So far we've handwaved the `` `(foo $bar) `` syntax to both create and
match on `Syntax` objects but it's time for a full explanation since
it will be essential to all non trivial things that are syntax related.

これまで、`Syntax`オブジェクトを作成し、マッチングするために
`` `(foo $bar) ``構文を手で振り回してきましたが、
これはすべての非自明な構文関連のものに不可欠なので、
完全な説明が必要です。


First things first we call the `` `() `` syntax a `Syntax` quotation.
When we plug variables into a syntax quotation like this: `` `($x) ``
we call the `$x` part an anti-quotation. When we insert `x` like this
it is required that `x` is of type `TSyntax x` where `x` is some `Name`
of a syntax category. The Lean compiler is actually smart enough to figure
the syntax categories that are allowed in this place out. Hence you might
sometimes see errors of the form:

まず第一に、`` `() ``構文を`Syntax`引用と呼びます。
`` `($x) ``のように変数を構文引用に挿入するとき、
`$x`部分をアンチクォーテーションと呼びます。
このように`x`を挿入すると、`x`が`TSyntax x`型である必要があります。
ここで`x`は構文カテゴリの`Name`です。
Leanコンパイラは、この場所で許可されている構文カテゴリを推測するのに十分に賢いです。
したがって、次のようなエラーが発生することがあります。
```
application type mismatch
  x.raw
argument
  x
has type
  TSyntax `a : Type
but is expected to have type
  TSyntax `b : Type
```
If you are sure that your thing from the `a` syntax category can be
used as a `b` here you can declare a coercion of the form:

`a`構文カテゴリのものがここで`b`として使用できることを確信している場合は、
次のようなコアーションを宣言できます。
TODO コアーションとは何か
-/

instance : Coe (TSyntax `a) (TSyntax `b) where
  coe s := ⟨s.raw⟩

/-!
Which will allow Lean to perform the type cast automatically. If you
notice that your `a` can not be used in place of the `b` here congrats,
you just discovered a bug in your `Syntax` function. Similar to the Lean
compiler, you could also declare functions that are specific to certain
`TSyntax` variants. For example as we have seen in the syntax chapter
there exists the function:

これにより、Leanは型キャストを自動的に実行できるようになります。
ここで、`a`を`b`の代わりに使用できないことに気付いたら、
`Syntax`関数のバグを発見したことになります。
Leanコンパイラと同様に、特定の`TSyntax`バリアントに固有の関数を宣言することもできます。
たとえば、構文章で見たように、次の関数が存在します。
-/
#check TSyntax.getNat -- TSyntax.getNat : TSyntax numLitKind → Nat
/-!
Which is guaranteed to not panic because we know that the `Syntax` that
the function is receiving is a numeric literal and can thus naturally
be converted to a `Nat`.

この関数はパニックしないことが保証されています。
なぜなら、関数が受け取る `Syntax` が数値リテラルであることを知っており、
それを自然に `Nat` に変換できるからです。

If we use the antiquotation syntax in pattern matching it will, as discussed
in the syntax chapter, give us a a variable `x` of type `` TSyntax y `` where
`y` is the `Name` of the syntax category that fits in the spot where we pattern matched.
If we wish to insert a literal `$x` into the `Syntax` for some reason,
for example macro creating macros, we can escape the anti quotation using: `` `($$x) ``.

パターンマッチングでアンチクォーテーション構文を使用すると、
構文章で説明したように、パターンマッチングする場所に合う構文カテゴリの`Name`である
`` TSyntax y ``型の変数`x`が得られます。
何らかの理由でリテラル`$x`を`Syntax`に挿入したい場合、
たとえばマクロを作成するマクロの場合、以下を用いてアンチクォーテーションをエスケープすることができます。
`` `($$x) ``。

If we want to specify the syntax kind we wish `x` to be interpreted as
we can make this explicit using: `` `($x:term) `` where `term` can be
replaced with any other valid syntax category (e.g. `command`) or parser
(e.g. `ident`). 

`x`をどのように解釈するかを指定したい場合は、
`` `($x:term) ``を使用してこれを明示的に行うことができます。
ここで、`term`は、他の有効な構文カテゴリ（たとえば`command`）
やパーサー（たとえば`ident`）に置き換えることができます。

So far this is only a more formal explanation of the intuitive things
we've already seen in the syntax chapter and up to now in this chapter,
next we'll discuss some more advanced anti-quotations.

これまで、これは構文章で既に見てきた直感的なもののより形式的な説明にすぎません。
次に、より高度なアンチクォーテーションについて説明します。

### Advanced anti-quotations
For convenience we can also use anti-quotations in a way similar to
format strings: `` `($(mkIdent `c)) `` is the same as: `` let x := mkIdent `c; `($x) ``.

便宜上、フォーマット文字列と同様の方法でアンチクォーテーションを使用することもできます。
`` `($(mkIdent `c)) ``は、`` let x := mkIdent `c; `($x) ``と同じです。

Furthermore there are sometimes situations in which we are not working
with basic `Syntax` but `Syntax` wrapped in more complex datastructures,
most notably `Array (TSyntax c)` or `TSepArray c s`. Where `TSepArray c s`, is a
`Syntax` specific type, it is what we get if we pattern match on some
`Syntax` that users a separator `s` to separate things from the category `c`.
For example if we match using: `$xs,*`, `xs` will have type `TSepArray c ","`,.
With the special case of matching on no specific separator (i.e. whitespace):
`$xs*` in which we will receive an `Array (TSyntax c)`.

さらに、基本的な`Syntax`ではなく、より複雑なデータ構造でラップされた`Syntax`を扱う場合があります。
特に、`Array (TSyntax c)`や`TSepArray c s`です。
`TSepArray c s`は、`Syntax`の特定の型です。
これは、カテゴリ`c`のものを区切り文字`s`で区切っている`Syntax`をパターンマッチングした場合に得られるものです。
たとえば、`$xs,*`を使用してマッチングすると、`xs`の型は`TSepArray c ","`になります。
区切り文字を指定しない場合（つまり、空白）の特別な場合は、`$xs*`で、
`Array (TSyntax c)`を受け取ります。

If we are dealing with `xs : Array (TSyntax c)` and want to insert it into
a quotation we have two main ways to achieve this:
1. Insert it using a separator, most commonly `,`: `` `($xs,*) ``.
  This is also the way to insert a `TSepArray c ",""`
2. Insert it point blank without a separator (TODO): `` `() ``

`xs : Array (TSyntax c)`を扱い、それを引用に挿入したい場合、
主に2つの方法があります。
1. 区切り文字（通常は`,`）を使用して挿入する：`` `($xs,*) ``。
  これは、`TSepArray c ",""`を挿入する方法でもあります。
2. 区切り文字なしでそのまま挿入する（TODO）：`` `() ``

For example:

たとえば：
-/

-- syntactically cut away the first element of a tuple if possible
syntax "cut_tuple " "(" term ", " term,+ ")" : term 

macro_rules
  -- cutting away one element of a pair isn't possible, it would not result in a tuple
  | `(cut_tuple ($x, $y)) => `(($x, $y)) 
  | `(cut_tuple ($x, $y, $xs,*)) => `(($y, $xs,*))

#check cut_tuple (1, 2) -- (1, 2) : Nat × Nat
#check cut_tuple (1, 2, 3) -- (2, 3) : Nat × Nat

/-!
The last thing for this section will be so called "anti-quotation splices".
There are two kinds of anti quotation splices, first the so called optional
ones. For example we might declare a syntax with an optional argument,
say our own `let` (in real projects this would most likely be a `let`
in some functional language we are writing a theory about):

このセクションの最後は、いわゆる「アンチクォーテーションスプライス」です。
アンチクォーテーションスプライスには2種類あります。
まず、オプションのものです。
たとえば、オプション引数を持つ構文を宣言することができます。
たとえば、私たち自身の`let`（実際のプロジェクトでは、おそらく私たちが理論を書いている
関数型言語の`let`であるでしょう）：

-/

syntax "mylet " ident (" : " term)? " := " term " in " term : term

/-!
There is this optional `(" : " term)?` argument involved which can let
the user define the type of the term to the left of it. With the methods
we know so far we'd have to write two `macro_rules` now, one for the case
with, one for the case without the optional argument. However the rest
of the syntactic translation works exactly the same with and without
the optional argument so what we can do using a splice here is to essentially
define both cases at once: 

ここでは、ユーザーがその左側の項の型を定義できるオプションの`(" : " term)?`引数があります。
これまでに知っている方法では、オプション引数の有無の場合に`macro_rules`を2つ書く必要があります。
しかし、オプション引数の有無に関係なく、構文変換の残りの部分はまったく同じように機能するので、
ここでスプライスを使用して、本質的に両方のケースを一度に定義できます。
-/

macro_rules
  | `(mylet $x $[: $ty]? := $val in $body) => `(let $x $[: $ty]? := $val; $body)

/-!
The `$[...]?` part is the splice here, it basically says "if this part of
the syntax isn't there, just ignore the parts on the right hand side that
involve anti quotation variables involved here". So now we can run
this syntax both with and without type ascription:

ここでの`$[...]?`部分はスプライスです。
これは、基本的に「この構文のこの部分がない場合は、
ここで関係するアンチクォーテーション変数を含む右側の部分を無視してください」という意味です。
したがって、型指定子を付けて、型指定子を付けずに、この構文を実行できます。
-/

#eval mylet x := 5 in x - 10 -- 0, due to subtraction behaviour of `Nat`
#eval mylet x : Int := 5 in x - 10 -- -5, after all it is an `Int` now

/-!
The second and last splice might remind readers of list comprehension
as seen for example in Python. We will demonstrate it using an implementation
of `map` as a macro:

2番目で最後のスプライスは、Pythonなどで見られるリスト内包表記を読者に思い出させるかもしれません。
マクロとしての`map`の実装を使用して、それを示します。
-/

-- run the function given at the end for each element of the list
syntax "foreach " "[" term,* "]" term : term

macro_rules
  | `(foreach [ $[$x:term],* ] $func:term) => `(let f := $func; [ $[f $x],* ])
  -- | `(foreach [ $[$x:term],* ] $func:term) => `([ $[$func $x],* ]) -- this would be wrong

#eval foreach [1,2,3,4] (Nat.add 2) -- [3, 4, 5, 6]

/-!
In this case the `$[...],*` part is the splice. On the match side it tries
to match the pattern we define inside of it repetitively (given the separator
we tell it to). However unlike regular separator matching it does not
give us an `Array` or `SepArray`, instead it allows us to write another
splice on the right hand side that gets evaluated for each time the
pattern we specified matched, with the specific values from the match
per iteration.

この場合、`$[...],*`部分がスプライスです。
マッチ側では、それが定義したパターンを繰り返し（指定した区切り文字で）マッチさせようとします。
しかし、通常の区切り文字のマッチングとは異なり、
`Array`や`SepArray`を返すのではなく、
指定したパターンがマッチした回数ごとに右側の別のスプライスを書くことができます。
この場合、マッチごとに評価されます。
-/

/-!
## Hygiene issues and how to solve them
If you are familiar with macro systems in other languages like C you
probably know about so called macro hygiene issues already.
A hygiene issue is when a macro introduces an identifier that collides with an
identifier from some syntax that it is including. For example:

他の言語のマクロシステム、たとえばCの場合、おそらく「マクロの衛生状態」と呼ばれる問題について
既に知っているかもしれません。
衛生問題とは、マクロが、それが含んでいる構文の識別子と衝突する識別子を導入するときのことです。
たとえば：
-/

-- Applying this macro produces a function that binds a new identifier `x`.
-- マクロを適用すると、新しい識別子`x`をバインドする関数が生成されます。
macro "const" e:term : term => `(fun x => $e)

-- But `x` can also be defined by a user
-- しかし、`x`はユーザーによっても定義されています。
def x : Nat := 42

-- Which `x` should be used by the compiler in place of `$e`?
-- コンパイラは`$e`の代わりにどの`x`を使用すべきですか？
#eval (const x) 10 -- 42

/-
Given the fact that macros perform only syntactic translations one might
expect the above `eval` to return 10 instead of 42: after all, the resulting
syntax should be `(fun x => x) 10`. While this was of course not the intention
of the author, this is what would happen in more primitive macro systems like
the one of C. So how does Lean avoid these hygiene issues? You can read
about this in detail in the excellent [Beyond Notations](https://lmcs.episciences.org/9362/pdf)
paper which discusses the idea and implementation in Lean in detail.
We will merely give an overview of the topic, since the details are not
that interesting for practical uses. The idea described in Beyond Notations
comes down to a concept called "macro scopes". Whenever a new macro
is invoked, a new macro scope (basically a unique number) is added to
a list of all the macro scopes that are active right now. When the current
macro introduces a new identifier what is actually getting added is an
identifier of the form:

マクロがシンタクティックな変換のみを実行するという事実を考えると
上記の`eval`が42ではなく10を返すことを期待するかもしれません。
結局のところ、結果の構文は`(fun x => x) 10`であるべきです。
これはもちろん、著者の意図ではありませんでしたが、
これはCのようなより原始的なマクロシステムでは起こることです。
では、Leanはどのようにしてこれらの衛生問題を回避しているのでしょうか？
優れた[Beyond Notations](https://lmcs.episciences.org/9362/pdf)論文では、
Leanでのアイデアと実装について詳しく説明しています。
私たちは、実際の使用にはあまり興味がないので、このトピックの概要を説明します。
Beyond Notationsで説明されているアイデアは、
「マクロスコープ」と呼ばれる概念にまで遡ります。
新しいマクロが呼び出されるたびに、
現在アクティブなすべてのマクロスコープのリストに新しいマクロスコープ（基本的には一意の数値）が追加されます。
現在のマクロが新しい識別子を導入するとき、
実際に追加されるのは次の形式の識別子です。
```
<actual name>._@.(<module_name>.<scopes>)*.<module_name>._hyg.<scopes>
```
For example, if the module name is `Init.Data.List.Basic`, the name is
`foo.bla`, and macros scopes are [2, 5] we get:

例えば、モジュール名が`Init.Data.List.Basic`で、名前が`foo.bla`で、
マクロスコープが[2, 5]の場合、
```
foo.bla._@.Init.Data.List.Basic._hyg.2.5
```
Since macro scopes are unique numbers the list of macro scopes appended in the end
of the name will always be unique across all macro invocations, hence macro hygiene
issues like the ones above are not possible.

マクロのスコープは固有の番号であるため、名前の最後に追加されるマクロスコープのリストは、
すべてのマクロ呼び出しにわたって常に一意であります。
したがって、上記のようなマクロハイジーンの問題は発生しません。

If you are wondering why there is more than just the macro scopes to this
name generation, that is because we may have to combine scopes from different files/modules.
The main module being processed is always the right most one.
This situation may happen when we execute a macro generated in a file
imported in the current file.

もし、この名前生成にマクロスコープ以上のものがなぜ存在するのか疑問に思っているなら、
それは、異なるファイル/モジュールからスコープを組み合わせる必要があるかもしれないからです。
処理されるメインモジュールは常に最も右側にあります。
この状況は、現在のファイルにインポートされたファイルで生成されたマクロを実行するときに発生する可能性があります。

```
foo.bla._@.Init.Data.List.Basic.2.1.Init.Lean.Expr_hyg.4
```
The delimiter `_hyg` at the end is used just to improve performance of
the function `Lean.Name.hasMacroScopes` -- the format could also work without it.

末尾のデリミタ`_hyg`は、関数`Lean.Name.hasMacroScopes`の性能を向上させるためだけに使用されます
 -- このフォーマットは、それなしでも動作します。

This was a lot of technical details. You do not have to understand them
in order to use macros, if you want you can just keep in mind that Lean
will not allow name clashes like the one in the `const` example.

これは多くの技術的な詳細です。
マクロを使用するためにこれらを理解する必要はありません。
もし望むなら、`const`の例のような名前の衝突はLeanが許可しないことを心に留めておくことができます。

Note that this extends to *all* names that are introduced using syntax
quotations, that is if you write a macro that produces:
`` `(def foo := 1) ``, the user will not be able to access `foo`
because the name will subject to hygiene. Luckily there is a way to
circumvent this. You can use `mkIdent` to generate a raw identifier,
for example: `` `(def $(mkIdent `foo) := 1) ``. In this case it won't
be subject to hygiene and accessible to the user.

これは、構文の引用を使用して導入される*すべて*の名前に拡張されることに注意してください。
つまり、次のようなマクロを書く場合：`` `(def foo := 1) ``、
ユーザーは`foo`にアクセスできません。
なぜなら、その名前は衛生状態になるからです。
幸いなことに、これを回避する方法があります。
`mkIdent`を使用して生の識別子を生成することができます。
たとえば：`` `(def $(mkIdent `foo) := 1) ``。
この場合、衛生状態にならず、ユーザーがアクセスできます。


## `MonadQuotation` and `MonadRef`
Based on this description of the hygiene mechanism one interesting
question pops up, how do we know what the current list of macro scopes
actually is? After all in the macro functions that were defined above
there is never any explicit passing around of the scopes happening.
As is quite common in functional programming, as soon as we start
having some additional state that we need to bookkeep (like the macro scopes)
this is done with a monad, this is the case here as well with a slight twist.

このハイジーンメカニズムの説明に基づいて、面白い質問が一つ浮かびます。
実際には、現在のマクロスコープのリストが何であるかを私たちはどう知っているのでしょうか？
結局のところ、上記で定義されたマクロ関数では、
スコープの明示的な渡しは何も起こりません。
関数型プログラミングでは非常に一般的ですが、
（マクロスコープのように）ブックキープする必要のある追加の状態があるとすぐに、
モナドを使用してこれを行います。
ここでも、少し変わった形で行われています。

Instead of implementing this for only a single monad `MacroM` the general
concept of keeping track of macro scopes in monadic way is abstracted
away using a type class called `MonadQuotation`. This allows any other
monad to also easily provide this hygienic `Syntax` creation mechanism
by simply implementing this type class.

`MacroM`の単一のモナドに対してのみこれを実装する代わりに、
マクロスコープをモナド的な方法で追跡する一般的な概念は、
`MonadQuotation`と呼ばれる型クラスを使用して抽象化されます。
これにより、他のどのモナドでも、この衛生的な`Syntax`作成メカニズムを簡単に提供できます。
単にこの型クラスを実装するだけです。

This is also the reason that while we are able to use pattern matching on syntax
with `` `(syntax) `` we cannot just create `Syntax` with the same
syntax in pure functions: there is no `Monad` implementing `MonadQuotation`
involved in order to keep track of the macro scopes.

これはまた、`` `(syntax) ``で構文をパターンマッチングできる一方で、
純粋な関数で同じ構文で`Syntax`を作成することはできない理由でもあります。
マクロスコープを追跡するために`MonadQuotation`を実装する`Monad`が関与していないからです。

Now let's take a brief look at the `MonadQuotation` type class:

さて、`MonadQuotation`型クラスを簡単に見てみましょう。
-/

namespace Playground

class MonadRef (m : Type → Type) where
  getRef      : m Syntax
  withRef {α} : Syntax → m α → m α

class MonadQuotation (m : Type → Type) extends MonadRef m where
  getCurrMacroScope : m MacroScope
  getMainModule     : m Name
  withFreshMacroScope {α : Type} : m α → m α

end Playground

/-
Since `MonadQuotation` is based on `MonadRef`, let's take a look at `MonadRef`
first. The idea here is quite simple: `MonadRef` is meant to be seen as an extension
to the `Monad` typeclass which
- gives us a reference to a `Syntax` value with `getRef`
- can evaluate a certain monadic action `m α` with a new reference to a `Syntax`
  using `withRef`

`MonadQuotation`は`MonadRef`に基づいているので、まずは`MonadRef`を見てみましょう。
ここでのアイデアは非常に単純です。
`MonadRef`は、`Monad`型クラスの拡張として見られることを意図しています。
- `getRef`で`Syntax`値への参照を得る
- `withRef`を使用して、新しい`Syntax`への参照である特定のモナドアクション`m α`を評価する

On it's own `MonadRef` isn't exactly interesting, but once it is combined with
`MonadQuotation` it makes sense.

`MonadRef`自体はあまり興味深くありませんが、`MonadQuotation`と組み合わせると意味があります。

As you can see `MonadQuotation` extends `MonadRef` and adds 3 new functions:
- `getCurrMacroScope` which obtains the latest `MacroScope` that was created
- `getMainModule` which (obviously) obtains the name of the main module,
  both of these are used to create these hygienic identifiers explained above
- `withFreshMacroScope` which will compute the next macro scope and run
  some computation `m α` that performs syntax quotation with this new
  macro scope in order to avoid name clashes. While this is mostly meant
  to be used internally whenever a new macro invocation happens, it can sometimes
  make sense to use this in our own macros, for example when we are generating
  some syntax block repeatedly and want to avoid name clashes.

見ての通り、`MonadQuotation`は`MonadRef`を拡張し、3つの新しい関数を追加します：
- `getCurrMacroScope`は、作成された最新の`MacroScope`を取得します。
- `getMainModule`は（明らかに）メインモジュールの名前を取得します。
  これらは、上記で説明した衛生的な識別子を作成するために使用されます。
- `withFreshMacroScope`は、次のマクロスコープを計算し、
  この新しいマクロスコープで構文引用を実行する計算`m α`を実行します。
  これは、新しいマクロ呼び出しが発生するたびに内部で使用することを意図していますが、
  自分自身のマクロでこれを使用することもあります。
  たとえば、何度も構文ブロックを生成し、名前の衝突を避けたい場合などです。

How `MonadRef` comes into play here is that Lean requires a way to indicate
errors at certain positions to the user. One thing that wasn't introduced
in the `Syntax` chapter is that values of type `Syntax` actually carry their
position in the file around as well. When an error is detected, it is usually
bound to a `Syntax` value which tells Lean where to indicate the error in the file.
What Lean will do when using `withFreshMacroScope` is to apply the position of
the result of `getRef` to each introduced symbol, which then results in better
error positions than not applying any position.

ここで`MonadRef`がどのように関与するかというと、
Leanはユーザーに対して特定の位置でエラーを指摘する方法を必要とします。
`Syntax`の章で紹介されていないことの1つは、
`Syntax`型の値がファイル内の位置を持っているということです。
エラーが検出されると、通常は`Syntax`値にバインドされ、
Leanにエラーをファイル内のどこに指摘するかを伝えます。
`withFreshMacroScope`を使用すると、
導入された各シンボルに`getRef`の結果の位置を適用します。
これにより、位置を適用しない場合よりも良いエラー位置が得られます。

To see error positioning in action, we can write a little macro that makes use of it:

エラー位置を確認するために、それを利用する小さなマクロを書いてみましょう。
-/

syntax "error_position" ident : term

macro_rules
  | `(error_position all) => Macro.throwError "Ahhh"
  -- the `%$tk` syntax gives us the Syntax of the thing before the %,
  -- in this case `error_position`, giving it the name `tk`

  -- `%$tk`構文は、`%`の前のものの構文を与えてくれます。
  -- この場合は`error_position`で、名前は`tk`です。
  | `(error_position%$tk first) => withRef tk (Macro.throwError "Ahhh")

#eval error_position all -- the error is indicated at `error_position all`
#eval error_position first -- the error is only indicated at `error_position`

/-
Obviously controlling the positions of errors in this way is quite important
for a good user experience.

明らかに、この方法でエラーの位置を制御することは、良いユーザー体験にとって非常に重要です。

## Mini project
As a final mini project for this section we will re-build the arithmetic
DSL from the syntax chapter in a slightly more advanced way, using a macro
this time so we can actually fully integrate it into the Lean syntax.

このセクションの最後のミニプロジェクトとして、
構文の章で構築した算術DSLを、今回はマクロを使用して、
Lean構文に完全に統合できるように、少し高度な方法で再構築します。
-/
declare_syntax_cat arith

syntax num : arith
syntax arith "-" arith : arith
syntax arith "+" arith : arith
syntax "(" arith ")" : arith
syntax "[Arith|" arith "]" : term

macro_rules
  | `([Arith| $x:num]) => `($x)
  | `([Arith| $x:arith + $y:arith]) => `([Arith| $x] + [Arith| $y]) -- recursive macros are possible
  | `([Arith| $x:arith - $y:arith]) => `([Arith| $x] - [Arith| $y])
  | `([Arith| ($x:arith)]) => `([Arith| $x])

#eval [Arith| (12 + 3) - 4] -- 11

/-! Again feel free to play around with it. If you want to build more complex
things, like expressions with variables, maybe consider building an inductive type
using macros instead. Once you got your arithmetic expression term
as an inductive, you could then write a function that takes some form of
variable assignment and evaluates the given expression for this
assignment. You could also try to embed arbitrary `term`s into your
arith language using some special syntax or whatever else comes to your mind.

もちろん、自由に試して遊んでみてください。
変数を含む式などのより複雑なものを構築したい場合は、
代わりにマクロを使用して帰納的な型を構築することを検討してください。
算術式の項を帰納的なものとして取得したら、
何らかの形の変数割り当てを取り、
この割り当てに対して与えられた式を評価する関数を書くことができます。
また、特別な構文や他の思いつくものを使用して、
任意の`term`をあなたの算術言語に埋め込むこともできます。
-/

/-!
## More elaborate examples
### Binders 2.0
As promised in the syntax chapter here is Binders 2.0. We'll start by
reintroducing our theory of sets:

構文の章で約束したように、ここでBinders 2.0を紹介します。
まず、集合の理論を再導入します。
-/
def Set (α : Type u) := α → Prop
def Set.mem (x : α) (X : Set α) : Prop := X x

-- Integrate into the already existing typeclass for membership notation
-- 既存のメンバーシップ表記の型クラスに統合する
instance : Membership α (Set α) where
  mem := Set.mem

def Set.empty : Set α := λ _ => False

-- the basic "all elements such that" function for the notation
-- 構文のための基本的な「すべての要素は」関数
def setOf {α : Type} (p : α → Prop) : Set α := p

/-!
The goal for this section will be to allow for both `{x : X | p x}`
and `{x ∈ X, p x}` notations. In principle there are two ways to do this:
1. Define a syntax and macro for each way to bind a variable we might think of
2. Define a syntax category of binders that we could reuse across other
   binder constructs such as `Σ` or `Π` as well and implement macros for
   the `{ | }` case

この章のゴールは、`{x : X | p x}`と`{x ∈ X, p x}`の両方の表記を許可することです。
原理的には、2つの方法があります。
1. 変数をバインドする方法ごとに、構文とマクロを定義する
2. `Σ`や`Π`などの他のバインダー構成で再利用できるバインダーの構文カテゴリを定義し、
   `{ | }`の場合のマクロを実装する

In this section we will use approach 2 because it is more easily reusable.

このセクションでは、再利用性が高いため、アプローチ2を使用します。
-/

declare_syntax_cat binder_construct
syntax "{" binder_construct "|" term "}" : term

/-!
Now let's define the two binders constructs we are interested in:

さて、興味のある2つのバインダー構成を定義しましょう。
-/
syntax ident " : " term : binder_construct
syntax ident " ∈ " term : binder_construct

/-!
And finally the macros to expand our syntax:

最後に、構文を展開するマクロです。
-/

macro_rules
  | `({ $var:ident : $ty:term | $body:term }) => `(setOf (fun ($var : $ty) => $body))
  | `({ $var:ident ∈ $s:term | $body:term }) => `(setOf (fun $var => $var ∈ $s ∧ $body))

-- Old examples with better syntax:
#check { x : Nat | x ≤ 1 } -- setOf fun x => x ≤ 1 : Set Nat

example : 1 ∈ { y : Nat | y ≤ 1 } := by simp[Membership.mem, Set.mem, setOf]
example : 2 ∈ { y : Nat | y ≤ 3 ∧ 1 ≤ y } := by simp[Membership.mem, Set.mem, setOf]

-- New examples:
def oneSet : Set Nat := λ x => x = 1
#check { x ∈ oneSet | 10 ≤ x } -- setOf fun x => x ∈ oneSet ∧ 10 ≤ x : Set Nat

example : ∀ x, ¬(x ∈ { y ∈ oneSet | y ≠ 1 }) := by
  intro x h
  -- h : x ∈ setOf fun y => y ∈ oneSet ∧ y ≠ 1
  -- ⊢ False
  cases h
  -- : x ∈ oneSet
  -- : x ≠ 1
  contradiction


/-!
## Reading further
If you want to know more about macros you can read:
- the API docs: TODO link
- the source code: the lower parts of [Init.Prelude](https://github.com/leanprover/lean4/blob/master/src/Init/Prelude.lean)
  as you can see they are declared quite early in Lean because of their importance
  to building up syntax
- the aforementioned [Beyond Notations](https://lmcs.episciences.org/9362/pdf) paper
-/
