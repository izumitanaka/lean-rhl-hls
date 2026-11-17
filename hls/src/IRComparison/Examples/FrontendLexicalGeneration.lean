import IRComparison.Frontend.WordFixedFunctionCompleteness
import IRComparison.Frontend.WordLexicalScalarCode
import IRComparison.Frontend.LeanHLSCommand
import IRComparison.Examples.FrontendSourceMatching

/-! Ordinary Lean definitions exercise the general source-derivation theorem.
The source evidence is built before calling the compiler. These examples do
not replace the syntax induction in LexicalScalarCode.Source.complete. -/
namespace IRComparison.FrontendLexicalGeneration
open Lean Elab Command WordFrontend FrontendSourceMatching
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic
set_option maxHeartbeats 1800000
set_option linter.unusedVariables false

def retainedArithmetic (i x y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  some (s.set 0 (let v : HybridWord.Word := s.regs 1; v + v))

def betaArithmetic (i x y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  some (s.set 0 ((fun v : HybridWord.Word => v + v) (s.regs 1)))

def regions : FixedMemory.Declarations := #[]

private def valueRaw := app ``HybridWord.State.regs [parameters.s,NatNotation.elaborated.native 1]
private def bodyRaw := Lean.mkApp2 Binary.add.nativeHeader (.bvar 0) (.bvar 0)
private def outputCode : HybridWord.Expr := .add (.reg 1) (.reg 1)
private def outputQuote := app ``HybridWord.Expr.add [app ``HybridWord.Expr.reg [NatNotation.elaborated.native 1],
  app ``HybridWord.Expr.reg [NatNotation.elaborated.native 1]]
private def outputValue (s : HybridWord.State) : Option HybridWord.Word := some (s.regs 1 + s.regs 1)

private theorem scalar_source (beta : Bool) (binder : Lean.Name) (flag : Bool) (info : Lean.BinderInfo) :
    LexicalScalarCode.Source StandardLibrary.model context parameters []
      (if beta then .app (.lam binder word bodyRaw info) valueRaw else .letE binder word valueRaw bodyRaw flag)
      (fun _ _ _ s _ => outputValue s) outputCode outputQuote := by
  let library := StandardLibrary.library
  have value : LexicalScalarCode.Source StandardLibrary.model context parameters [] valueRaw
      (fun _ _ _ s _ => some (s.regs 1)) (.reg 1) (app ``HybridWord.Expr.reg [NatNotation.elaborated.native 1]) := by
    apply LexicalScalarCode.Source.register 1 .elaborated rfl rfl
    exact ⟨by decide,by decide,by decide,by intro k; rfl⟩
  let binding : LexicalScalarCode.Value := ⟨valueRaw,fun _ _ _ s _ => some (s.regs 1),.reg 1,
    app ``HybridWord.Expr.reg [NatNotation.elaborated.native 1]⟩
  -- One reference-based construction is instantiated in both environments.
  -- There is no second arithmetic induction for the open body.
  have body {env ctx p} (bound : LexicalScalarCode.Value) (tail : List LexicalScalarCode.Value)
      (separated : ScalarSyntax.Separated p (LexicalScalarCode.expand (bound::tail) bodyRaw)) :
      LexicalScalarCode.Source env ctx p (bound::tail) bodyRaw
        (fun i x y s ls => (bound.native i x y s ls).bind (fun u =>
          (bound.native i x y s ls).bind (fun v => some (u + v))))
        (.add bound.code bound.code) (app ``HybridWord.Expr.add [bound.quotation,bound.quotation]) :=
    .binary .add (.reference rfl) (.reference rfl) separated
  have sum := body (env := StandardLibrary.model) (ctx := context) (p := parameters) binding []
    ⟨by decide,by decide,by decide,by intro k; rfl⟩
  have openSum := body (env := StandardLibrary.model) (ctx := wordType::context) (p := parameters.lift)
    ⟨.bvar 0,fun _ _ _ _ ls => ls[0]?,.local 0,app ``HybridWord.Expr.local [(ClosedTerm.bindingIndex 0).val]⟩ []
    ⟨by decide,by decide,by decide,by intro k; rfl⟩
  let inputs := Certificate.initialInputs library.connection.word library.connection.nilWords
  cases beta with
  | false =>
    exact LexicalScalarCode.Source.letOpen library StandardLibrary.closed inputs
      .initial (by intro v h; cases h) .word value sum openSum binder flag
  | true =>
    exact LexicalScalarCode.Source.betaOpen library StandardLibrary.closed inputs
      .initial (by intro v h; cases h) .word value sum openSum binder info

hls_word retainedArithmetic as retainedArithmeticHLS
hls_word betaArithmetic as betaArithmeticHLS
example : retainedArithmeticHLS.wordBody = .assign 0 outputCode := rfl
example : betaArithmeticHLS.wordBody = .assign 0 outputCode := rfl
example : (fun s => (outputValue s).bind (fun v => some (s.set 0 v))) = retainedArithmetic 0 0 0 := rfl
example : (fun s => (outputValue s).bind (fun v => some (s.set 0 v))) = betaArithmetic 0 0 0 := rfl
def retainedBitsLiteral (i x y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  some (s.set 0 (let v : BitVec 32 := 4294967297; v))

private theorem identity_source (annotation : WordBinder.Annotation)
    (value : LexicalScalarCode.Source StandardLibrary.model context parameters [] v f vc vq)
    (beta : Bool) (binder : Name) (flag : Bool) (info : BinderInfo) :
    LexicalScalarCode.Source StandardLibrary.model context parameters []
      (if beta then .app (.lam binder annotation.native (.bvar 0) info) v
       else .letE binder annotation.native v (.bvar 0) flag) f vc vq := by
  have ref : LexicalScalarCode.Source StandardLibrary.model context parameters
      [⟨LexicalScalarCode.expand [] v,f,vc,vq⟩] (.bvar 0) f vc vq :=
    .reference (n := 0) (bound := ⟨LexicalScalarCode.expand [] v,f,vc,vq⟩) rfl
  have openRef := LexicalScalarCode.Source.reference (env := StandardLibrary.model)
    (ctx := annotation.core::context) (p := parameters.lift)
    (vs := LexicalScalarCode.openValues []) (n := 0) (by rfl)
  let library := StandardLibrary.library
  let inputs := Certificate.initialInputs library.connection.word library.connection.nilWords
  cases beta with
  | false =>
    exact LexicalScalarCode.Source.letOpen library StandardLibrary.closed inputs .initial
      (by intro v h; cases h) annotation value ref openRef binder flag
  | true =>
    exact LexicalScalarCode.Source.betaOpen library StandardLibrary.closed inputs .initial
      (by intro v h; cases h) annotation value ref openRef binder info

private theorem annotated_let_source (annotation : WordBinder.Annotation) (n : Nat)
    (binder : Lean.Name) (flag : Bool) :
    LexicalScalarCode.Source StandardLibrary.model context parameters []
      (.letE binder annotation.native (AnnotatedLiteral.native annotation n) (.bvar 0) flag)
      (fun _ _ _ _ _ => some (BitVec.ofNat 32 n)) (.lit (BitVec.ofNat 32 n))
      (app ``HybridWord.Expr.lit [AnnotatedLiteral.native annotation n]) := by
  have scope : ScalarSyntax.Separated parameters (AnnotatedLiteral.native annotation n) := by
    cases annotation <;> exact ⟨rfl,rfl,rfl,by intro k; rfl⟩
  have value := LexicalScalarCode.Source.annotatedLiteral (env := StandardLibrary.model)
    (ctx := context) (vs := []) annotation n scope
  exact identity_source annotation value false binder flag .default

hls_word retainedBitsLiteral as retainedBitsLiteralHLS
example : retainedBitsLiteralHLS.wordBody = .assign 0 (.lit 1) := rfl
example : (fun s => some (s.set 0 (BitVec.ofNat 32 4294967297))) = retainedBitsLiteral 0 0 0 := rfl

/-- Keep both beta nodes in the elaborated input. Substitution changes the
inferred result annotation of the inner expression, not its BV32 meaning. -/
def mixedBinderWord (i x y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  some (s.set 0 (let v : HybridWord.Word := (fun w : BitVec 32 => w) 4294967297; v))

def mixedBinderBits (i x y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  some (s.set 0 (let v : BitVec 32 := (fun w : HybridWord.Word => w) 4294967297; v))

private theorem mixed_binder_source (outer inner : WordBinder.Annotation) (n : Nat)
    (bn wn : Name) (flag : Bool) (info : BinderInfo) :
    LexicalScalarCode.Source StandardLibrary.model context parameters []
      (.letE bn outer.native (.app (.lam wn inner.native (.bvar 0) info) (AnnotatedLiteral.native inner n)) (.bvar 0) flag)
      (fun _ _ _ _ _ => some (BitVec.ofNat 32 n)) (.lit (BitVec.ofNat 32 n))
      (app ``HybridWord.Expr.lit [AnnotatedLiteral.native inner n]) := by
  have value := LexicalScalarCode.Source.annotatedLiteral (env := StandardLibrary.model)
    (ctx := context) (p := parameters) (vs := []) inner n
    (by cases inner <;> exact ⟨rfl,rfl,rfl,by intro k; rfl⟩)
  have applied := identity_source inner value true wn false info
  exact identity_source outer applied false bn flag .default

hls_word mixedBinderWord as mixedBinderWordHLS
hls_word mixedBinderBits as mixedBinderBitsHLS
example : mixedBinderWordHLS.wordBody = .assign 0 (.lit 1) := rfl
example : mixedBinderBitsHLS.wordBody = .assign 0 (.lit 1) := rfl
example : (fun s => some (s.set 0 (BitVec.ofNat 32 4294967297))) = mixedBinderWord 0 0 0 := rfl
example : (fun s => some (s.set 0 (BitVec.ofNat 32 4294967297))) = mixedBinderBits 0 0 0 := rfl

/-- The inner body uses the outer retained value, not its newest binder. -/
def retainedCapture (i x y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  some (s.set 0 (let outer : HybridWord.Word := s.regs 1; let inner : BitVec 32 := outer; outer))

/-- A single body construction works under both an open and a substituted
outer binder. Its environment and retained value are universally quantified. -/
private theorem captured_body {env ctx p} (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (inputs : InputsTyped env ctx p)
    (typing : LexicalScalarCode.ScopeTyped env ctx p) (retained : LexicalScalarCode.Value)
    (typed : LexicalScalarCode.Evidence env ctx retained.source)
    (annotation : WordBinder.Annotation) (binder : Name) (flag : Bool) :
    LexicalScalarCode.Source env ctx p [retained]
      (.letE binder annotation.native (.bvar 0) (.bvar 1) flag)
      retained.native retained.code retained.quotation := by
  have values : LexicalScalarCode.ValuesTyped env ctx [retained] := by
    intro v h
    rcases List.mem_cons.mp h with rfl | h
    · exact typed
    · cases h
  have value := LexicalScalarCode.Source.reference (env := env) (ctx := ctx) (p := p)
    (vs := [retained]) (n := 0) (by rfl)
  have next := LexicalScalarCode.Source.reference (env := env) (ctx := ctx) (p := p)
    (vs := [⟨LexicalScalarCode.expand [retained] (.bvar 0),retained.native,retained.code,retained.quotation⟩,retained])
    (n := 1) (by rfl)
  have opened := LexicalScalarCode.Source.reference (env := env) (ctx := annotation.core::ctx) (p := p.lift)
    (vs := LexicalScalarCode.openValues [retained]) (n := 1) (by rfl)
  exact LexicalScalarCode.Source.letOpen library closed inputs typing values annotation value next opened binder flag

private theorem capture_source (outer inner : Name) (outerFlag innerFlag : Bool) :
    LexicalScalarCode.Source StandardLibrary.model context parameters []
      (.letE outer word valueRaw (.letE inner WordBinder.Annotation.bitvec.native (.bvar 0) (.bvar 1) innerFlag) outerFlag)
      (fun _ _ _ s _ => some (s.regs 1)) (.reg 1) (app ``HybridWord.Expr.reg [NatNotation.elaborated.native 1]) := by
  let library := StandardLibrary.library
  let inputs := Certificate.initialInputs library.connection.word library.connection.nilWords
  have typing : LexicalScalarCode.ScopeTyped StandardLibrary.model context parameters := .initial
  have values : LexicalScalarCode.ValuesTyped StandardLibrary.model context [] := by intro v h; cases h
  have value : LexicalScalarCode.Source StandardLibrary.model context parameters [] valueRaw
      (fun _ _ _ s _ => some (s.regs 1)) (.reg 1) (app ``HybridWord.Expr.reg [NatNotation.elaborated.native 1]) := by
    apply LexicalScalarCode.Source.register 1 .elaborated rfl rfl
    exact ⟨by decide,by decide,by decide,by intro k; rfl⟩
  have next := captured_body library StandardLibrary.closed inputs typing
    ⟨LexicalScalarCode.expand [] valueRaw,fun _ _ _ s _ => some (s.regs 1),.reg 1,
      app ``HybridWord.Expr.reg [NatNotation.elaborated.native 1]⟩
    (value.evidence library.scalars library.decisions inputs typing values) .bitvec inner innerFlag
  have opened := captured_body library StandardLibrary.closed (inputs.lift StandardLibrary.closed wordType)
    (typing.lift StandardLibrary.closed wordType)
    ⟨.bvar 0,fun _ _ _ _ ls => ls[0]?,.local 0,app ``HybridWord.Expr.local [(ClosedTerm.bindingIndex 0).val]⟩
    (LexicalScalarCode.Evidence.variable .word .zero) .bitvec inner innerFlag
  exact LexicalScalarCode.Source.letOpen library StandardLibrary.closed inputs typing values .word value next opened outer outerFlag

hls_word retainedCapture as retainedCaptureHLS
example : retainedCaptureHLS.wordBody = .assign 0 (.reg 1) := rfl
example : (fun s => some (s.set 0 (s.regs 1))) = retainedCapture 0 0 0 := rfl

end IRComparison.FrontendLexicalGeneration
