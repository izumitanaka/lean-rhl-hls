# 通常のLean入力の保証と、RTLまでの接続


## 現在の最上位保証

[`OrdinarySource.generates`](../src/IRComparison/Frontend/WordOrdinarySourceInterpretation.lean)は、**元の通常Lean構文と独立した型・束縛・静的条件から、実際の`StructuralBody.compileRetained`の成功、生成コードとの対応、固定配列Entryの構成、RTL生成成功まで**を接続する。

```text
名前付きLean定義・標準環境の条件（NativeEnvironment.Input）
元の本体の構文・変数型・配列宣言（OrdinarySource.Body）
元のState使用条件（Body.Current）、静的なレジスタ番号
宣言の一意性・公開出力が宣言済み
    ↓ Body.syntaxEntry（関数／本体の共通の相互帰納法）
既存のFunctionSyntax.Syntax：保持後・展開後の条件はここで導出
    ↓ generatesRetainedSyntaxInstalled
compileRetained成功＋CodeTyped＋Sourceによる生成コードとの対応
    ↓ SourceからFixedHLS.Entryを構成
Entry.compile_total → SystemVerilog RTL生成成功
```

最終定理の前提には、解析成功、生成済みEntry、内部検査成功、`CastTyping`、保持後本体の判断や本体族を置かない。`Source`と`Syntax`は引き続き内部の合成・生成成功証明として再利用する。ここで使うのは証明用の元構文判断とその解釈であり、ユーザー向けDSLや実行IRではない。実行する変換器・意味論・後段は変更していない。

### 入口規則と、内部で導く条件

| 元の入力側に書くこと | 一般証明で導く内部条件 |
|---|---|
| 補助関数の元のラムダ本体を一度、元の署名、各実引数の構文・型、捕捉するStateの使用条件 | 捕捉環境、実引数保持後の環境と本体Syntax、元のラムダ型・部分適用型・後続型、保持用let列の型。`FunctionMeaning.ofLambda`／`ArgumentBindings.heldEnvironment`／`FunctionMeaning.invoke` |
| `let s := ...`／`let s ← ...`の元の値・処理と、新しいState変数を使う元の後続本体 | `CurrentMapping`、更新後の型・参照・捕捉環境、後続Syntax。`stateLetSyntax`／`stateBindSyntax`と`Body.Flow.interpret` |
| `let v ← (s.arrays a)[k]?`の元の読出しと、値変数を使う元の後続本体 | 読出し型と宣言整合性、値保持後の参照位置・Word/BV32型変換、後続Syntax。`Read.forms`／`readBindSyntax`と同じ帰納法 |
| スカラlet／βの元の値と、束縛変数を残した元本体 | 開いた側と代入側のForm、束縛の型・値参照。`Scalar.forms`と既存の`openValues`／`openBody`等を使う共通接続 |

`FunctionMeaning`、`BodyMeaning`、`ScalarFrame`などは帰納法の結論・不変条件であり、入口の新しい前提ではない。関数を宣言してから値・State・読出し・ループの束縛を挟んで使う場合も、同じ捕捉環境の移送を使う。元本体と保持後本体を、構文ごとに利用側で二度導出する必要はなくなった。

### 対象構文の対応表

以下は`WordOrdinarySource.lean`の元構文を、`Body.Flow.interpret`／`Function.Flow.interpret`の**一つの相互帰納法**で覆う。子は任意の同じ判断であり、例の深さ・引数個数・組合せに固定しない。

| 対象形式 | 元の判断／共通接続 | 状態 |
|---|---|---|
| Word/BV32リテラル、局所値、レジスタ、四則演算、符号反転、ゼロ／非ゼロによる値の選択 | `Scalar` → `Scalar.forms` | 接続済み |
| スカラ内部のlet／即時ラムダ適用 | `Scalar.letValue`／`beta` → 共通の束縛・代入の証明 | 接続済み |
| State返却、レジスタ更新、反復継続 | `StateValue`、`Body.returns`／`yield` | 接続済み |
| 固定配列読出し、書込み、同長配列間の全体コピー | `Read`、`Body.write`／`copy`、`Read.forms` | 接続済み |
| スカラ・Stateのlet、State／読出しのdo束縛、逐次処理 | `letScalar`／`letState`／`bindState`／`bindRead` | 接続済み |
| 条件分岐、実際のdo展開のPUnit継続 | `branch`／`unitSequence` | 接続済み |
| `HybridWord.range`、リテラル・負号・四則演算による静的なInt境界 | `staticRange`／`StaticBound` → `staticRangeSyntax` | 接続済み |
| `List.range n.toNat`のforIn／foldlM、Nat反復番号のBV32化 | `naturalRange`／`Scalar.natural` → `naturalRangeSyntax` | 接続済み |
| 補助関数の即時適用、局所定義・参照・捕捉、Word/BV32混在引数 | `Function`／`Body.call`／`letFunction`、`FunctionMeaning`の構成 | 接続済み |
| 上記の分岐・反復・束縛・補助関数の任意の入れ子／組合せ | 同じ相互帰納法、引数保持環境は一つの引数列の帰納法 | 接続済み |

この表は任意のLean式を含むという意味ではない。元の通常Lean表記は、現在の対応する展開形で上記の判断を満たす必要がある。任意の再帰、一般の高階関数、任意の閉じたLean式の正規化を追加したわけではない。

### 残る前提と保証の境界

- `NativeEnvironment.Input`は元定義の型・ヘッダ、標準宣言、有限の署名依存閉包、閉じた型、名前の条件。`NativeEnvironment.input`が実環境から証拠付きで構成し、`input_complete`が独立条件から構成成功を示す。利用側に内部`Library`や`CastTyping`を手書きさせない。
- 固定配列入口の本体は初期Stateを使う。互換用の先頭3個のWord引数を本体が参照しないという既存の条件を、`Body ds [.value .state]`に明示する。任意の引数を持つLean関数全般への保証ではない。
- 配列ID・長さは事前宣言し、IDは一意、読書き先と公開出力は宣言済み、全体コピー先と元は同長。個々の配列アクセスの実行時成功は生成成功の前提ではない。
- State更新／逐次処理の後続は最新のStateを使う。スカラの古い値の保持は許す。呼出し引数も呼出し時の値を保持し、本体のState更新後に再評価しない。
- 補助関数の実引数は既存のState／PUnit／Word／BitVec 32呼出し規約。Nat反復変数・そのBV32化は対象だが、任意のNat値をそのまま渡す補助関数呼出しはこの規約に含まれない。型の補助判断がNatを表現できることと、呼出し規約の範囲を混同しない。
- 生成成功と意味保存は別の主張。`generates`は生成物の存在・コード型・元本体とのSource対応を返す。実行結果の保存は既存の`Source.computation`、EntryおよびRTLの正しさ定理を使う。全入力で元計算が成功すること、任意初期状態の外部ポート設定可能性、物理タイミングを新たに証明していない。
- 型処理の必要な予算の十分性は既存の生成成功証明を通じて利用する。型変換・簡約の予算の整理は別課題。旧解析器や互換経路は現行ビルドに残していない。最適化予算と回路実行サイクルも別であり、最適化予算は引き続き残す。

通常Lean定義への適用は[`OrdinarySourceExamples`](../src/IRComparison/Examples/OrdinarySourceExamples.lean)で確認する。具体例は一般証明の代替ではない。最上位定理の前提に、解析成功や生成済みEntryは置かない。

## 入力を書く

固定配列の入口は`hls_fixed_program`。配列番号と長さは事前宣言し、コピーは宣言済みの領域間で行う。

```lean
import IRComparison.Frontend.LeanHLSCommand
open IRComparison HybridWord

def buffers : FixedMemory.Declarations := #[(0,4),(1,4)]

def program (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for i in HybridWord.range 0 3 1 do
    t ← t.copy 1 0 4
    let v ← (t.arrays 1)[i.toNat]?
    t ← t.write 0 i (v+1)
  return t

hls_fixed_program program using buffers as generated
#check generated.compile
#check generated.correct
#check generated.generates
```

`range start stop stride`は、正の歩幅なら終点未満、負なら終点より大きい間を反復する。対象は生成時に確定する始点・終点・正または負の歩幅。本体は反復回数ぶん展開せず、構文の子を解析する。例えば`range 6 (-1) (-2)`の添字は6,4,2,0。実行用ヘルパーの歩幅0は空範囲だが、対象構文とは区別する。

`copy destination source count`の個数は、事前宣言した両配列の長さと一致させる。計算中の配列確保・拡張、更新前State全体の再利用は対象外。古いスカラ値をletで保存することと、宣言済みの別配列へコピーして内容を保存することはできる。

このコマンドが公開する`generated.generates`は、構成された固定配列Entryからの生成成功を使う。**元のLean構文から解析成功までを含む一般定理は別に`OrdinarySource.generates`である。** コマンドが実行できた例だけから、構文全体の成功を結論していない。

## 入口の使い分け

| 入口 | 与えるもの・役割 |
|---|---|
| `hls_word` | BV32本体を解析し、生成コードと元Lean定義の接続証明を登録する |
| `hls_certified` | カーネル本体と外側の反復・配列等の情報を、メモリ最適化とRTLの全体保証へ接続する |
| `hls_program` | 関数全体のループ・処理順をソースから取り出す。固定配列の検査を追加する前の入口 |
| `hls_fixed_program` | 関数全体と固定配列宣言を渡す。Entryを構成し、`compile`／`correct`／`generates`を登録する |

通常の解析は全て`StructuralBody.compileRetained`を使う。関数全体からFIFO化用の処理列を自動抽出する機能と、構文全体の生成成功は別であり、前者は今後の拡張である。処理列を明示する既存の入口では、バッファ挿入・配列単位のFIFO化を利用できる。

## 生成成功と意味保存

```text
元の限定構文・型・スコープ・固定配列・環境条件
  ⇒ compileRetained成功 ∧ 生成コードとの対応 ∧ Entry構成 ∧ RTL生成成功

生成された回路 + 配置・入力・初期状態などの実行条件
  ⇒ 有限サイクルで終了し、元Lean計算の成功／失敗と公開出力を保つ
```

前者は`OrdinarySource.generates`、後者は`Source.computation`と`FixedHLS.Entry.compile_correct`等の既存の全体定理を使う。`CertifiedHLS.ProgramEntry.compile_correct`、`CertifiedHLS.Compiled.correct`は、元のLean関数／処理列と出力SystemVerilog文字列の実行をつなぐ。

観測するのは終了・失敗・公開出力。内部FIFOや保持レジスタの配置、失敗後の途中状態の一致は要求しない。配列の範囲外読出し等で元計算が失敗する場合まで、全入力での正常終了を主張しない。

## 信頼境界と予算

Leanの実装、環境からの定義取得・宣言登録を信頼する。接続証明項はLeanカーネルで検査する。任意のLean式の正規化、Leanのエラボレータやコンパイラ自体の正しさを証明したとは主張しない。

本体・ループ本体・スカラの走査は構文の減少で停止し、旧解析器へのフォールバックはない。型変換に残る予算、最適化探索の時間予算、回路の実行サイクル数は別物。最適化予算切れでは採用済みの証明付き計画を保持する。

SystemVerilogは定義した二値部分言語。IEEE全体の四値・イベント意味論、外部EDAツール、同期RAMの遅延、物理タイミングは保証対象外。32ビット外部ポートの適合条件と、任意初期状態の設定可能性は[外部ポート](HLS-SYNTAX-RULES.ja.md#外部ポートと初期設定)を参照。

## 検証方法

[再現手順](../../docs/REPRODUCING.md)のビルド、公理監査、通常入口回帰を使用する。生成成功の一般定理と、例に対する検査は区別する。検証ログや開発履歴はこの公開版には同梱しない。
