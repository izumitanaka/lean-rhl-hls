# 通常Lean関数からバッファ挿入・FIFO化へ

`hls_fixed_program`は、関数内の処理列からステージを自動抽出し、既存のバッファ挿入・配列単位のFIFO選択へ渡す。処理列・反復範囲・対象配列を別途手書きする必要はない。固定配列宣言と公開出力は引き続き指定する。

```lean
hls_fixed_program program using declarations as generated
-- 純粋な候補探索を使う通常の入口
-- generated.compile [outputArray]
-- SMTを補助として使う入口（ログの保存先も指定する）
-- generated.compileWithSMT [outputArray] "artifacts/my-program/smt"
```

## 抽出するものと保持するもの

- 順次処理をソース順に分解する。順序の変更・融合・並列化は行わない。
- `HybridWord.range`に由来する静的範囲ループは、本体・始点・歩幅・反復回数として取り出す。逆走査と非単位歩幅も同じ構成を使う。
- IRの`forRange`で回数がリテラルになっているものも取り出す。これには対応する定数回数の`List.range`／`foldlM`が含まれる。
- ループ変数の束縛をステージの反復値へ接続する。本体内のスカラ束縛、分岐、入れ子のループはそのまま保つ。展開して反復回数分のコードを作ることはない。
- 対象配列は、本体が読み出し、本体内では書き換えない宣言済み配列から選ぶ。プログラム内で生成される配列を優先し、同順位では宣言順を使う。最終的なFIFO化は既存の全体計画検査で判断する。

外側の値束縛をまたぐ分割、条件分岐内部の処理列の独立ステージ化、動的回数ループの外側反復への抽出は行わない。その部分は一つの処理としてコンパイルする。例えば、State更新前のスカラ値を保存して二つのループで使う場合、その束縛をまたいで分割したり、引数を更新後のStateから再評価したりしない。これは最適化の適用範囲であり、入力言語の制限追加ではない。

一つのステージで複数配列をFIFO入力にする等の既存最適化器の制約も変えていない。自動抽出できることと、FIFO化できることは別である。

## 一般証明と通常入口への接続

| 対象 | 一般定理 | 結論 |
|---|---|---|
| ループ変数・局所束縛の接続 | `AutomaticStages.indexExpr_correct`／`indexBody_correct` | 任意の対象本体・束縛環境について、値・更新・失敗を保つ |
| 処理列の抽出 | `AutomaticStages.pieces_correct` | 抽出した処理列の逐次実行が元のCmdの実行と一致する |
| 配列宣言 | `pieces_declared`／`entry_closed` | 新たな配列参照を導入せず、抽出した全ステージが既存配置の条件を満たす |
| 元のLean関数との対応 | `FixedHLS.Entry.staged_correct` | 自動抽出したステージ列の実行が元の通常Lean関数と一致する |
| 生成成功 | `FixedHLS.Entry.compile_total` | 宣言済み公開出力について、自動抽出・最適化・RTL生成が成功する |
| 意味保存 | `FixedHLS.Entry.compile_correct`／`artifact_correct` | 既存の実行・初期状態の条件下で、RTLの有限クロック実行が元のLean関数の成功／失敗と公開出力を保つ |

[抽出器と証明](../src/IRComparison/Frontend/AutomaticStages.lean)、[通常入口への接続](../src/IRComparison/Frontend/FixedHLS.lean)。

最上位の`OrdinarySource.generates`は同じ独立した構文・型・静的条件から`Entry.compile_total`へ接続しているため、今回も解析成功や生成済みEntryを前提に追加しない。`generated.correct`と`generated.generates`も自動抽出後の入口に対する定理になる。`generated.artifact_correct`はSMT経由も含む証明付き生成物に使える。

SMT応答の再検査、探索期限、採用済み計画の保持は既存の仕組みを使う。外部検索が失敗した場合も、純粋なコンパイル経路が利用できる。

## 回帰確認

```sh
lake env lean --run scripts/automatic-stages.lean
python3 scripts/check-automatic-stages.py
```

[通常Lean入力の例と検査](../scripts/automatic-stages.lean)では、順走査、逆走査、順序不一致、歩幅2、疎な配列ID、保持値の寿命、自然数範囲、分岐を含む複数入力、範囲外アクセス、ゼロ反復、SMT経由を扱う。100万回の静的反復も、抽出結果が1本のループのままであることを確認する。

生成・消費の両方が歩幅2の例は、現在のアフィンなFIFOルーティング検査ではメモリ維持となる。一方、単位歩幅で生成し歩幅2で消費する例では、不要値を破棄してFIFO化できる。前者の制約は既存のルーティング解析によるもので、自動抽出が歩幅を1に限定しているわけではない。

生成RTLと検査ログは`artifacts/automatic-stages/`へ出力する。外部検査は設定・再起動・公開出力・エラーフラグを確認し、物理タイミングは対象にしない。
