/-
# Embedding DSLs By Elaboration

In this chapter we will learn how to use elaboration to build a DSL. We will not
explore the full power of `MetaM`, and simply gesture at how to get access to
this low-level machinery.

この章では、エラボレーションを使用してDSLを構築する方法を学びます。
`MetaM`の全ての機能を探求することはありませんが、この低レベルの機構へのアクセス方法を示唆します。

More precisely, we shall enable Lean to understand the syntax of
[IMP](http://concrete-semantics.org/concrete-semantics.pdf),
which is a simple imperative language, often used for teaching operational and
denotational semantics.

より正確には、Leanが[IMP](http://concrete-semantics.org/concrete-semantics.pdf)
の構文を理解できるようにします。
IMPは、操作的および指示的セマンティクスの教育のためによく使用されるシンプルな命令型言語です。

We are not going to define everything with the same encoding that the book does.
For instance, the book defines arithmetic expressions and boolean expressions.
We, will take a different path and just define generic expressions that take
unary or binary operators.

私たちは、その本が行うのと同じエンコーディングで全てを定義するわけではありません。
例えば、その本では算術式やブール式を定義しています。
私たちは異なるアプローチを取り、単項または二項演算子を取る一般的な式を定義するだけです。

This means that we will allow weirdnesses like `1 + true`! But it will simplify
the encoding, the grammar and consequently the metaprogramming didactic.

これは、`1 + true`のような奇妙な式も許容することを意味します！
しかし、これによりエンコーディングや文法が簡略化され、
結果としてメタプログラミングの教育的側面も簡略化されます。

## Defining our AST

We begin by defining our atomic literal value.

まず、私たちは原子的なリテラル値を定義します。
-/

import Lean

open Lean Elab Meta

inductive IMPLit
  | nat  : Nat  → IMPLit
  | bool : Bool → IMPLit

/- This is our only unary operator -/
inductive IMPUnOp
  | not

/- These are our binary operations. -/

inductive IMPBinOp
  | and | add | less

/- Now we define the expressions that we want to handle. -/

inductive IMPExpr
  | lit : IMPLit → IMPExpr
  | var : String → IMPExpr
  | un  : IMPUnOp → IMPExpr → IMPExpr
  | bin : IMPBinOp → IMPExpr → IMPExpr → IMPExpr

/-
And finally the commands of our language. Let's follow the book and say that
"each piece of a program is also a program":

そして、私たちの言語のコマンドを最終的に定義します。
本に従い、"プログラムの各部分もまたプログラムである"と言いましょう：
-/

inductive IMPProgram
  | Skip   : IMPProgram
  | Assign : String → IMPExpr → IMPProgram
  | Seq    : IMPProgram → IMPProgram → IMPProgram
  | If     : IMPExpr → IMPProgram → IMPProgram → IMPProgram
  | While  : IMPExpr → IMPProgram → IMPProgram

/-
## Elaborating literals

Now that we have our data types, let's elaborate terms of `Syntax` into
terms of `Expr`. We begin by defining the syntax and an elaboration function for
literals.

データ型を持つようになったので、`Syntax`の項を`Expr`の項へと展開しましょう。
リテラルのための構文と展開関数を定義することから始めます。
-/

declare_syntax_cat imp_lit
syntax num       : imp_lit
syntax "true"    : imp_lit
syntax "false"   : imp_lit

def elabIMPLit : Syntax → MetaM Expr
  -- `mkAppM` creates an `Expr.app`, given the function `Name` and the args
  -- `mkNatLit` creates an `Expr` from a `Nat`
  | `(imp_lit| $n:num) => mkAppM ``IMPLit.nat  #[mkNatLit n.getNat]
  | `(imp_lit| true  ) => mkAppM ``IMPLit.bool #[.const ``Bool.true []]
  | `(imp_lit| false ) => mkAppM ``IMPLit.bool #[.const ``Bool.false []]
  | _ => throwUnsupportedSyntax

elab "test_elabIMPLit " l:imp_lit : term => elabIMPLit l

#reduce test_elabIMPLit 4     -- IMPLit.nat 4
#reduce test_elabIMPLit true  -- IMPLit.bool true
#reduce test_elabIMPLit false -- IMPLit.bool false

/-
## Elaborating expressions

In order to elaborate expressions, we also need a way to elaborate our unary and
binary operators.

式を展開するためには、単項演算子と二項演算子を展開する方法も必要です。

Notice that these could very much be pure functions (`Syntax → Expr`), but we're
staying in `MetaM` because it allows us to easily throw an error for match
completion.

これらは純粋な関数（`Syntax → Expr`）である可能性があることに注意してください。
しかし、`MetaM`にとどまっているのは、マッチングの完了のために簡単にエラーを投げることができるからです。
-/

declare_syntax_cat imp_unop
syntax "not"     : imp_unop

def elabIMPUnOp : Syntax → MetaM Expr
  | `(imp_unop| not) => return .const ``IMPUnOp.not []
  | _ => throwUnsupportedSyntax

declare_syntax_cat imp_binop
syntax "+"       : imp_binop
syntax "and"     : imp_binop
syntax "<"       : imp_binop

def elabIMPBinOp : Syntax → MetaM Expr
  | `(imp_binop| +)   => return .const ``IMPBinOp.add []
  | `(imp_binop| and) => return .const ``IMPBinOp.and []
  | `(imp_binop| <)   => return .const ``IMPBinOp.less []
  | _ => throwUnsupportedSyntax

/-Now we define the syntax for expressions: -/

declare_syntax_cat                   imp_expr
syntax imp_lit                     : imp_expr
syntax ident                       : imp_expr
syntax imp_unop imp_expr           : imp_expr
syntax imp_expr imp_binop imp_expr : imp_expr

/-
Let's also allow parentheses so the IMP programmer can denote their parsing
precedence.

IMPプログラマが構文解析の優先順位を示すことができるように、括弧も許可しましょう。
-/

syntax "(" imp_expr ")" : imp_expr

/-
Now we can elaborate our expressions. Note that expressions can be recursive.
This means that our `elabIMPExpr` function will need to be recursive! We'll need
to use `partial` because Lean can't prove the termination of `Syntax`
consumption alone.

これで私たちの式を具体化することができます。
式は再帰的になることに注意してください。
これは、私たちの`elabIMPExpr`関数も再帰的である必要があることを意味します！
Leanは`Syntax`の消費だけで終了を証明することはできないので、
`partial`を使用する必要があります。
-/

partial def elabIMPExpr : Syntax → MetaM Expr
  | `(imp_expr| $l:imp_lit) => do
    let l ← elabIMPLit l
    mkAppM ``IMPExpr.lit #[l]
  -- `mkStrLit` creates an `Expr` from a `String`
  | `(imp_expr| $i:ident) => mkAppM ``IMPExpr.var #[mkStrLit i.getId.toString]
  | `(imp_expr| $b:imp_unop $e:imp_expr) => do
    let b ← elabIMPUnOp b
    let e ← elabIMPExpr e -- recurse!
    mkAppM ``IMPExpr.un #[b, e]
  | `(imp_expr| $l:imp_expr $b:imp_binop $r:imp_expr) => do
    let l ← elabIMPExpr l -- recurse!
    let r ← elabIMPExpr r -- recurse!
    let b ← elabIMPBinOp b
    mkAppM ``IMPExpr.bin #[b, l, r]
  | `(imp_expr| ($e:imp_expr)) => elabIMPExpr e
  | _ => throwUnsupportedSyntax

elab "test_elabIMPExpr " e:imp_expr : term => elabIMPExpr e

#reduce test_elabIMPExpr a
-- IMPExpr.var "a"

#reduce test_elabIMPExpr a + 5
-- IMPExpr.bin IMPBinOp.add (IMPExpr.var "a") (IMPExpr.lit (IMPLit.nat 5))

#reduce test_elabIMPExpr 1 + true
-- IMPExpr.bin IMPBinOp.add (IMPExpr.lit (IMPLit.nat 1)) (IMPExpr.lit (IMPLit.bool true))

/-
## Elaborating programs

And now we have everything we need to elaborate our IMP programs!

そして、今、私たちのIMPプログラムを詳細化するために必要なすべてが揃いました！
-/

declare_syntax_cat           imp_program
syntax "skip"              : imp_program
syntax ident ":=" imp_expr : imp_program

syntax imp_program ";;" imp_program : imp_program

syntax "if" imp_expr "then" imp_program "else" imp_program "fi" : imp_program
syntax "while" imp_expr "do" imp_program "od" : imp_program

partial def elabIMPProgram : Syntax → MetaM Expr
  | `(imp_program| skip) => return .const ``IMPProgram.Skip []
  | `(imp_program| $i:ident := $e:imp_expr) => do
    let i : Expr := mkStrLit i.getId.toString
    let e ← elabIMPExpr e
    mkAppM ``IMPProgram.Assign #[i, e]
  | `(imp_program| $p₁:imp_program ;; $p₂:imp_program) => do
    let p₁ ← elabIMPProgram p₁
    let p₂ ← elabIMPProgram p₂
    mkAppM ``IMPProgram.Seq #[p₁, p₂]
  | `(imp_program| if $e:imp_expr then $pT:imp_program else $pF:imp_program fi) => do
    let e ← elabIMPExpr e
    let pT ← elabIMPProgram pT
    let pF ← elabIMPProgram pF
    mkAppM ``IMPProgram.If #[e, pT, pF]
  | `(imp_program| while $e:imp_expr do $pT:imp_program od) => do
    let e ← elabIMPExpr e
    let pT ← elabIMPProgram pT
    mkAppM ``IMPProgram.While #[e, pT]
  | _ => throwUnsupportedSyntax

/-
And we can finally test our full elaboration pipeline. Let's use the following
syntax:

最後に、私たちの完全な詳細化パイプラインをテストすることができます。
以下の構文を使用しましょう：
-/

elab ">>" p:imp_program "<<" : term => elabIMPProgram p

#reduce >>
a := 5;;
if not a and 3 < 4 then
  c := 5
else
  a := a + 1
fi;;
b := 10
<<
-- IMPProgram.Seq (IMPProgram.Assign "a" (IMPExpr.lit (IMPLit.nat 5)))
--   (IMPProgram.Seq
--     (IMPProgram.If
--       (IMPExpr.un IMPUnOp.not
--         (IMPExpr.bin IMPBinOp.and (IMPExpr.var "a")
--           (IMPExpr.bin IMPBinOp.less (IMPExpr.lit (IMPLit.nat 3)) (IMPExpr.lit (IMPLit.nat 4)))))
--       (IMPProgram.Assign "c" (IMPExpr.lit (IMPLit.nat 5)))
--       (IMPProgram.Assign "a" (IMPExpr.bin IMPBinOp.add (IMPExpr.var "a") (IMPExpr.lit (IMPLit.nat 1)))))
--     (IMPProgram.Assign "b" (IMPExpr.lit (IMPLit.nat 10))))
