import PaperCore.Language
import Lean

/-! Paper-like surface syntax. Every construct expands directly into the existing
Source AST; no expression lowering, new state, or new operational semantics. -/
namespace PaperCore
open Lean

declare_syntax_cat pcInt
syntax num : pcInt
syntax "-" num : pcInt
syntax "#" ident : pcInt

declare_syntax_cat pcExpr
syntax pcInt : pcExpr
syntax ident : pcExpr
syntax ident "+" ident : pcExpr
syntax ident "-" ident : pcExpr
syntax ident "*" ident : pcExpr
syntax ident "/" ident : pcExpr
syntax ident "[op|" term "]" ident : pcExpr

declare_syntax_cat pcStmt
syntax ident ":=" pcExpr ";" : pcStmt
syntax ident ":=" ident "[" pcExpr "]" ";" : pcStmt
syntax ident "[" pcExpr "]" ":=" ident ";" : pcStmt
syntax "if" ident "then" "{" pcStmt+ "}" "else" "{" pcStmt+ "}" : pcStmt
syntax "for" ident ":=" pcExpr "to" pcInt "step" pcInt "{" pcStmt+ "}" : pcStmt
syntax "kernel" "{" pcStmt+ "}" : pcStmt

syntax "paper" "{" pcStmt+ "}" : term
syntax "paperInt%" pcInt : term
syntax "paperExpr%" pcExpr : term
syntax "paperStmt%" pcStmt : term

private def nameLiteral (x : TSyntax `ident) : TSyntax `term :=
  ⟨Syntax.mkStrLit x.getId.toString⟩

macro_rules
  | `(paperInt% $n:num) => `(($n : Int))
  | `(paperInt% - $n:num) => `(-($n : Int))
  | `(paperInt% # $n:ident) => `(($n : Int))
  | `(paperExpr% $n:pcInt) => `(Expr.num (paperInt% $n))
  | `(paperExpr% $x:ident) => `(Expr.var $(nameLiteral x))
  | `(paperExpr% $x:ident + $y:ident) => `(Expr.bin .add $(nameLiteral x) $(nameLiteral y))
  | `(paperExpr% $x:ident - $y:ident) => `(Expr.bin .sub $(nameLiteral x) $(nameLiteral y))
  | `(paperExpr% $x:ident * $y:ident) => `(Expr.bin .mul $(nameLiteral x) $(nameLiteral y))
  | `(paperExpr% $x:ident / $y:ident) => `(Expr.bin .div $(nameLiteral x) $(nameLiteral y))
  | `(paperExpr% $x:ident [op| $op:term ] $y:ident) =>
      `(Expr.bin $op $(nameLiteral x) $(nameLiteral y))
  | `(paperStmt% $x:ident := $e:pcExpr ;) =>
      `(Stmt.assign $(nameLiteral x) (paperExpr% $e))
  | `(paperStmt% $x:ident := $a:ident [$e:pcExpr] ;) =>
      `(Stmt.action (MemoryAction.read $(nameLiteral x) $(nameLiteral a) (paperExpr% $e)))
  | `(paperStmt% $a:ident [$e:pcExpr] := $x:ident ;) =>
      `(Stmt.action (MemoryAction.write $(nameLiteral a) (paperExpr% $e) $(nameLiteral x)))
  | `(paperStmt% if $x:ident then { $yes:pcStmt* } else { $no:pcStmt* }) =>
      `(Stmt.branch $(nameLiteral x) (paper { $yes* }) (paper { $no* }))
  | `(paperStmt% for $x:ident := $start:pcExpr to $stop:pcInt step $stride:pcInt { $body:pcStmt* }) =>
      `(Stmt.loop $(nameLiteral x) (paperExpr% $start) (paperInt% $stop)
        (paperInt% $stride) (paper { $body* }))
  | `(paperStmt% kernel { $body:pcStmt* }) => `(Stmt.kernel (paper { $body* }))
  | `(paper { $first:pcStmt $rest:pcStmt* }) =>
      if rest.isEmpty then `(paperStmt% $first)
      else `(Stmt.seq (paperStmt% $first) (paper { $rest* }))

end PaperCore
