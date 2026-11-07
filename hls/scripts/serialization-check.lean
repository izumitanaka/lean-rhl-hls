import IRComparison.Circuit.SystemVerilog.SerializationSound

open IRComparison.Circuit IRComparison.Circuit.SystemVerilog

-- These are decoder rejection / signed-width boundaries, not finite substitutes
-- for the general printer theorems in Lexical and LiteralTextSound.
example : Name.parse "e00" = none := by decide
example : Name.parse "e0" = some (.temporary 0) := by decide
example : Name.parse "r1;error" = none := by decide
example : Name.parse "cfg_data" = some .configData := by decide
example : decimal "".toList = none := by decide
example : decimal "12x".toList = none := by decide
example : signedDecimal "0'sd1" = none := by decide
example : signedDecimal "32'sd-1" = none := by decide
example : signedDecimal "32'd1" = none := by decide
example : signedDecimal "32'sd1;" = none := by decide
example : (signedTokenValue "1'sd1" none).map Value.integer = some (-1) := by decide
example : (signedTokenValue "32'sd4294967295" (some ⟨65,true⟩)).map Value.integer = some (-1) := by decide
example : (signedTokenValue "32'sd2147483648" none).map Value.integer = some (-2147483648) := by decide
example : (signedTokenValue "32'sd4294967296" none).map Value.integer = some 0 := by decide

private def emptyEnv : Environment :=
  ⟨fun _ => ⟨32,false⟩,fun _ => none,fun _ _ => none⟩

def main : IO Unit := do
  let values : List Int := [0,1,-1,127,128,-128,2147483647,2147483648,
    -2147483648,4294967295,4294967296,-4294967297,18446744073709551616]
  let mut declarations : List String := []
  let mut checks : List String := []
  let mut count := 0
  for width in [1,8,32,33,65] do
    for value in values do
      if positive : 0 < width then
        let e := Expr.literal width value positive
        for destWidth in [1,8,32,65] do
          let some expected := e.assignment emptyEnv destWidth
            | throw (IO.userError "literal assignment was undefined")
          let printed := Concrete.printExpression e
          let some parsedExpr := Concrete.parseExpression printed
            | throw (IO.userError "expression text did not parse")
          let some parsed := parsedExpr.eval emptyEnv (some ⟨destWidth,true⟩)
            | throw (IO.userError s!"literal token did not parse: {e.text}")
          unless (BitVec.ofInt destWidth parsed.integer).toNat == expected.toNat do
            throw (IO.userError s!"parsed/model value disagreement: {e.text}")
          declarations := declarations ++
            [s!"wire signed [{destWidth-1}:0] v{count} = {printed};"]
          checks := checks ++
            [s!"if (v{count} !== {destWidth}'d{expected.toNat}) $fatal(1, \"literal case {count}\");"]
          count := count+1
  let extra : List SystemVerilog.Expr := [
    .binary .add (.bit true) (.literal 32 (-1) (by decide)),
    .cast 8 (.integer 256) (by decide),
    .unsigned (.literal 8 (-1) (by decide)),
    .binary .lt (.literal 32 (-1) (by decide)) (.integer 0),
    .binary .div (.literal 8 (-7) (by decide)) (.literal 8 3 (by decide)),
    .binary .mod (.literal 8 (-7) (by decide)) (.literal 8 3 (by decide)),
    division (.literal 8 (-7) (by decide)) (.literal 8 3 (by decide)),
    .select (.bit false) (.literal 32 (-1) (by decide)) (.integer 255),
    .binary .mul (.integer 4294967295) (.integer 4294967295),
    .binary .and (.bit false) (.binary .div (.integer 1) (.integer 0))]
  for e in extra do
    for width in [1,8,32,65] do
      let printed := Concrete.printExpression e
      let some parsed := Concrete.parseExpression printed | throw (IO.userError "compound parse failed")
      let some expected := e.assignment emptyEnv width | throw (IO.userError "compound evaluation failed")
      unless (parsed.assignment emptyEnv width).map BitVec.toNat == some expected.toNat do
        throw (IO.userError "compound parsed evaluation differs")
      declarations := declarations ++ [s!"wire signed [{width-1}:0] v{count} = {printed};"]
      checks := checks ++ [s!"if (v{count} !== {width}'d{expected.toNat}) $fatal(1, \"compound case {count}\");"]
      count := count+1
  let sample : ModuleCode := {
    storage := [.scalar .pc 1 false,.scalar (.register 0) 32 false],wires := #[],
    read := ⟨[(0,.register 0)],[]⟩,reset := .skip,start := .skip,configure := .skip,
    cases := [.assign (.reference (.register 0)) (.binary .add (.integer 2) (.integer 3))],
    fault := .skip,controller := RTL.controller }
  let sampleText := sample.text
  unless (Concrete.parseModule sampleText).isSome do throw (IO.userError "whole module parse failed")
  for corrupted in [sampleText.replace "posedge" "negedge",sampleText.replace "read_valid" "other_valid",
      sampleText ++ " unexpected",sampleText.replace "hls_top" "other_top"] do
    unless (Concrete.parseModule corrupted).isNone do throw (IO.userError "corrupted interface/frame was accepted")
  let plus := Concrete.printExpression (.binary .add (.integer 2) (.integer 3))
  let some changed := Concrete.parseExpression (plus.replace "+" "-") | throw (IO.userError "valid operator mutation rejected")
  unless (changed.eval emptyEnv none).map Value.integer == some (-1) do
    throw (IO.userError "parser ignored changed operator text")
  let path := "artifacts/serialization"
  IO.FS.createDirAll path
  IO.FS.writeFile (path ++ "/literals.sv") <| String.intercalate "\n" <|
    ["module tb;"] ++ declarations ++ ["initial begin #1;"] ++ checks ++
    [s!"$display(\"PASS {count} expression width/sign cases\"); $finish; end", "endmodule", ""]
  IO.println s!"PASS {count} parsed/model cases; wrote {path}/literals.sv"
