import IRComparison.Circuit.SystemVerilog.Syntax

namespace IRComparison.Circuit.SystemVerilog

/-- Grammar of the concrete expression fragment. Productions use the native
SV tokens (including explicit cast, sign extension, and parentheses), not a
source-RTL expression or the output of the expression compiler. This grammar
does not yet establish evaluation or lexer/parser conformance. -/
inductive ExpressionText : String → Expr → Prop where
  | reference (name) : ExpressionText name.text (.reference name)
  | index {address name text} : ExpressionText text address →
      ExpressionText (name.text ++ "[" ++ text ++ "]") (.index name address)
  | integer (n) : ExpressionText (toString (bits n+1) ++ "'sd" ++ toString n) (.integer n)
  | literal (w n) (positive : 0 < w) :
      ExpressionText (toString w ++ "'sd" ++ toString (BitVec.ofInt w n).toNat) (.literal w n positive)
  | falseBit : ExpressionText "1'b0" (.bit false)
  | trueBit : ExpressionText "1'b1" (.bit true)
  | unsigned {e text} : ExpressionText text e →
      ExpressionText ("$signed({1'b0," ++ text ++ "})") (.unsigned e)
  | cast {w e text} {positive : 0 < w} : ExpressionText text e →
      ExpressionText ("$signed(" ++ toString w ++ "'(" ++ text ++ "))") (.cast w e positive)
  | binary {op a b left right} : ExpressionText left a → ExpressionText right b →
      ExpressionText ("(" ++ left ++ " " ++ op.text ++ " " ++ right ++ ")") (.binary op a b)
  | select {c a b cond yes no} : ExpressionText cond c → ExpressionText yes a → ExpressionText no b →
      ExpressionText ("(" ++ cond ++ " ? " ++ yes ++ " : " ++ no ++ ")") (.select c a b)

theorem Expr.text_correct (e : Expr) : ExpressionText e.text e := by
  induction e with
  | reference name => exact .reference name
  | index name address ih => exact .index ih
  | integer n => exact .integer n
  | literal w n positive => exact .literal w n positive
  | bit b => cases b <;> constructor
  | unsigned e ih => exact .unsigned ih
  | cast w e positive ih => exact .cast ih
  | binary op a b ha hb => exact .binary ha hb
  | select c a b hc ha hb => exact .select hc ha hb

inductive WireText : String → Wire → Prop where
  | declaration {w : Wire} {text} : ExpressionText text w.value →
      WireText ("  wire signed [" ++ toString (w.width-1) ++ ":0] " ++ w.name.text ++ " = " ++ text ++ ";") w

theorem Wire.text_correct (w : Wire) : WireText w.text w := .declaration w.value.text_correct

inductive DestinationText : String → Destination → Prop where
  | reference (name) : DestinationText name.text (.reference name)
  | index {name address text} : ExpressionText text address →
      DestinationText (name.text ++ "[" ++ text ++ "]") (.index name address)

theorem Destination.text_correct (d : Destination) : DestinationText d.text d := by
  cases d with
  | reference name => exact .reference name
  | index name address => exact .index address.text_correct

inductive StatementText : String → Statement → Prop where
  | skip : StatementText "" .skip
  | assign {target value left right} : DestinationText left target → ExpressionText right value →
      StatementText (left ++ " <= " ++ right ++ ";") (.assign target value)
  | seq {a b first second} : StatementText first a → StatementText second b →
      StatementText (first ++ " " ++ second) (.seq a b)
  | branch {c a b cond yes no} : ExpressionText cond c → StatementText yes a → StatementText no b →
      StatementText ("if (" ++ cond ++ ") begin " ++ yes ++ " end else begin " ++ no ++ " end") (.branch c a b)
  | forRange {loopVar count body text} : StatementText text body →
      StatementText ("for (reg [" ++ toString (bits count-1) ++ ":0] " ++ loopVar.text ++ "=0;" ++ loopVar.text ++ "<" ++ (Expr.integer count).text ++ ";" ++
        loopVar.text ++ "=" ++ loopVar.text ++ "+1) begin " ++ text ++ " end") (.forRange loopVar count body)

theorem Statement.text_correct (s : Statement) : StatementText s.text s := by
  induction s with
  | skip => exact .skip
  | assign target value => exact .assign target.text_correct value.text_correct
  | seq a b ha hb => exact .seq ha hb
  | branch c a b ha hb => exact .branch c.text_correct ha hb
  | forRange loopVar count body ih => exact .forRange ih

end IRComparison.Circuit.SystemVerilog
