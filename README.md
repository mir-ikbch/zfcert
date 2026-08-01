# ZFCert

一階述語論理と ZFC 集合論を対象とする、小さな OCaml 製定理証明支援系です。
証明スクリプトはサーバ側のカーネルで検査され、Web UI からすぐに試せます。

## Coqによる参照形式化

[coq/FOL.v](coq/FOL.v) に、一階述語論理と自然演繹を形式化しています。

- ZFCの項（de Bruijn indexによる変数と文字列名のグローバル定数）
- 等号、所属、論理結合子、全称・存在量化
- 定数を変化させず、捕獲を起こさないrenaming・代入・量化子の具体化
- Tarski型のモデル意味論
- 直観主義自然演繹（等号規則を含む）
- 全称仮定の具体化と矛盾除去
- 自然演繹の健全性定理 `natural_deduction_sound`
- モデルの存在を仮定した相対的無矛盾性 `relative_consistency`

[coq/ProofState.v](coq/ProofState.v) には、抽出可能な証明状態、`rule`と`tactic`、
実行関数`step`・`run`があります。`rule`は自然演繹のプリミティブな推論規則で、
`tactic`は`TacRule : rule -> tactic`に加えて`intro`, `exact`, `apply`,
`specialize`, `cases`, `split`, `left`, `right`, `use`, `refl`,
`contradiction`などの便利な操作を持ちます。

`step_sound`と`run_sound`は、変換後の全ゴールが導出可能なら変換前も導出可能であることを
任意の理論について証明します。特に`successful_run_derives`により、`run`が単一ゴールを
空の状態へ変換した場合、そのゴールには必ず`derives`の導出が存在します。
選言の枝選択などは証明探索を失敗させ得るため一般には双方向同値ではありませんが、
可逆な`intro`と`split`には個別の同値定理もあります。

[coq/TacticCompleteness.v](coq/TacticCompleteness.v) は、プリミティブ規則だけを
実行する`rule_step`・`rule_run`を定義します。
計算可能な公理判定器`is_axiom`が理論`T`に対して健全かつ完全、すなわち

```text
is_axiom A = true -> T A
T A -> is_axiom A = true
```

を満たすなら、`derives_iff_rule_success`により次が証明されています。

```text
derives T Γ C
<->
exists rules,
  rule_run is_axiom rules [Goal Γ C] = Success []
```

前向きの構成だけを述べる定理が`derives_has_rule_list`です。したがって
`Cut`や`EqualElim`を含むプリミティブ規則だけで、任意の`derives`の導出を
成功する有限列として実行できます。`map TacRule rules`を使うことで、同じ列を
タクティクとして適用できることも`run_rule_list`で証明しています。

[coq/NamedProofState.v](coq/NamedProofState.v) は、この論理核を文字列名で扱う
抽出可能な層です。論理式の変数、仮定、量化子導入、`cut`などに必要な名前を
Coq側で管理し、名前付きの`named_start`・`named_goals`・`named_step`・
`named_rule_run`を提供します。各名前付き遷移について、成功後の状態が証明可能なら
成功前も証明可能であることを、既存のde Bruijn核の健全性へ帰着して証明しています。
`named_start_with_constants`へ定数名の一覧を渡すと、それらは局所変数とは別に
`Const string`へ変換され、量化子の導入や代入では変化しません。同名の局所変数による
シャドーイングは拒否されます。

[coq/NamedCommands.v](coq/NamedCommands.v) は、固定ZFC公理、分出、置換の
表面コマンドを名前付きプリミティブ規則列へ展開します。公理図式のインスタンス、
freshな内部仮定名、規則列はCoq側で生成され、各実行関数の健全性も
`named_zfc_rule_run_sound`から証明されています。OCamlで解析された
`named_rule_request`は、抽出された`named_execute_rule`が実行します。

[coq/CertifiedSession.v](coq/CertifiedSession.v) は、公理能力を添えた
プリミティブ規則列を計算可能な証明書として保持します。`certified_finalize`は
初期命題から証明書を再実行し、成功時にはその命題について
`derives zfc_theory [] ...`が成り立つことを`certified_finalize_sound`で
証明しています。`certified_start_with_constants`で開始したセッションでは、定数環境も
証明書の再実行時に保存されます。

[coq/GlobalEnvironment.v](coq/GlobalEnvironment.v) は、文字列名の定数と、対応する
名前付き・de Bruijn形式の事実を揃えて保持する抽出可能なグローバル環境です。
`global_declare_choice`は既存環境の下で存在命題の証明書を再実行し、全ゴールが閉じた
場合だけ、新しい定数と具体化済み事実を追加します。受理された存在命題の導出可能性は
`global_declare_choice_source_sound`、環境遷移の形は
`global_declare_choice_extends_environment`で証明しています。

[coq/ZFC.v](coq/ZFC.v) には、空集合、外延性、対、和、冪集合、正則性、
無限、分出公理図式、置換公理図式、選択を明示的な論理式として収録しています。
任意の論理式を公理として受理する逃げ道はありません。
推論核は直観主義で、ZFCに必要な古典論理は排中律の公理図式
`ZFC_excluded_middle` として明示的に分離しています。

```sh
make coq
```

すべての証明は `Admitted` なしで検査されます。[coq/Audit.v](coq/Audit.v) は
主要定理の仮定を機械的に表示し、すべて `Closed under the global context` になることを
確認します。抽出された認証済みセッションは既存OCamlサーバーへ組み込まれており、
`Proof_session`が生成したプリミティブ規則列は抽出カーネルの`certified_run`で
検査・記録されます。現在のゴールも`Zfcert_kernel.goals`から名前付きのまま取得します。
パーサー、名前解決、HTTP/UIは従来のOCamlコードが担当します。

抽出用エントリポイントは[coq/ExtractProofState.v](coq/ExtractProofState.v)に分離して
あります。抽出物を更新するときは次を実行します。

```sh
make extract
```

生成物は`extracted/proof_state.ml`で、名前付きの規則検査器に加え、
`certified_start`, `certified_run`, `certified_finalize`と、
固定公理・分出・置換を証明書へ展開する関数、グローバル環境を開始・拡張する
`global_start`, `global_declare_choice`を含みます。
単独のOCamlコンパイルも確認しています。

抽出された`Proof_state`モジュールはDuneのprivate moduleとして隠蔽されています。
外部へ公開するのは[extracted/zfcert_kernel.mli](extracted/zfcert_kernel.mli)だけで、
証明状態とグローバル環境は構築子を持たない抽象型`Zfcert_kernel.state`、
`Zfcert_kernel.environment`です。初期状態は抽出された
`certified_start`、以後の状態は抽出された認証済み規則実行関数の返り値としてのみ
取得できます。この抽象状態は初期命題、現在のゴール、受理済みの規則証明書を一体で
保持します。

OCamlサーバーが保持する論理状態の正本もこの抽象`state`です。セッションには
表示用のゴールや名前メタデータを重複して保持しません。仮定とゴールは毎回
`Zfcert_kernel.goals`から取得します。論理状態は抽出APIの返した値だけで更新し、
`qed`では記録済みの全プリミティブ規則を初期命題から再実行し、全ゴールが閉じることを
ダブルチェックします。Web UIでは検査後に`Show checked primitive rules`を開くと、
この証明書を表示できます。
公理判定関数を外側から渡すAPIも公開せず、固定ZFC公理または分出・置換から作られた
抽象的な公理能力だけを各証明書ステップへ添付します。

## OCamlソースの構成

- `src/syntax.ml`: 論理式の構文木、表示、自由変数、捕獲回避代入、α同値
- `src/parser.ml`: 字句解析、論理式の優先順位解析、複数行の文と終端`.`の解析
- `src/kernel_syntax.ml`: パーサー構文と抽出された名前付き構文の単純な構築子変換
- `src/rule_parser.ml`: `rule`文を型付きの名前付き規則要求へ変換する純粋なパーサー
- `src/proof_session.ml`: 定義の展開、抽出APIの直接実行、対話的証明状態
- `src/api_json.ml`: 証明状態とエラーのJSON表現
- `src/http_server.ml`: HTTPと静的ファイルの入出力
- `src/self_test.ml`: 証明カーネルの回帰試験
- `src/cli.ml`: コマンドライン引数とサーバー起動
- `src/main.ml`: `Cli.run`を呼ぶだけのエントリポイント

`Parser`は`Syntax`だけに依存し、証明状態やHTTP層には依存しません。
`Kernel_syntax`は論理式の構築子を対応付けるだけで、変数の番号付けや
証明状態の更新は行いません。
`Rule_parser`は現在のゴールや証明状態を参照せず、文字列の構文と引数だけを解析します。
ゴール形状、仮定名・変数名のfreshness、公理図式の適用は抽出カーネルが検査します。
`Proof_session`は抽象型`Zfcert_kernel.state`と`Zfcert_kernel.environment`を保持し、
その状態とグローバル宣言を
`Zfcert_kernel`の認証済み規則実行関数以外では変更できません。`apply`や複数項の
`specialize`を含む表面タクティクはOCaml側で規則列を計画するだけであり、その列の
実行、蓄積、終了時再検査は抽出コードが担当します。raw抽出モジュール
`Proof_state`は引き続きprivate moduleであり、アプリケーション層からアクセスできません。

依存関係は次の一方向です。

```text
Web / VS Code / Emacs
          |
      HTTP + JSON
          |
    Proof_session
      /       |       \
     v        v        v
 Parser  Rule_parser  Zfcert_kernel facade
              |              |
              v              |
        Kernel_syntax        |
                             |
               Coq-extracted Proof_state (private)
```

APIの成功・エラー・進捗メッセージとWeb UIは英語に統一しています。

## VS Code拡張

[zfcert-vscode-0.2.0.vsix](zfcert-vscode-0.2.0.vsix) をVS Codeの
`Extensions: Install from VSIX...` からインストールできます。拡張のソースは
[vscode-zfcert](vscode-zfcert) にあります。

インストール後、このリポジトリをVS Codeで開き、
[examples/specialize.zfp](examples/specialize.zfp) を開いてください。
カーソル位置までの証明が自動検査され、ZFCertサイドバーに現在の仮定とゴールが
表示されます。カーネルはポート8099で自動起動します。

- カーソル位置まで実行: `Cmd+Alt+Enter` / `Ctrl+Alt+Enter`
- 証明全体を検査: `Cmd+Alt+Shift+Enter` / `Ctrl+Alt+Shift+Enter`
- コマンドパレット: `ZFCert: Restart Kernel`

開発版はルートワークスペースをVS Codeで開き、`Run ZFCert Extension`を
デバッグ実行して試せます。

## Emacs拡張

[emacs-zfcert/zfcert-mode.el](emacs-zfcert/zfcert-mode.el)を`load-path`へ追加すると、
`.zfp`用の`zfcert-mode`を利用できます。

```elisp
(add-to-list 'load-path "/path/to/ZFCert/emacs-zfcert")
(require 'zfcert-mode)
```

`C-c C-RET`でカーソル行まで実行し、`C-c C-n`で次の行まで実行して
カーソルをその行へ移動します。`C-c C-c`で証明全体を検査します。
仮定とゴールは`*ZFCert Goals*`バッファに表示されます。カーネルの自動起動、
エラー行の強調、構文強調にも対応しています。設定と全キーバインドは
[Emacs拡張のREADME](emacs-zfcert/README.md)を参照してください。

## 起動

OCaml 5.x と Dune 3.x が必要です。

```sh
dune build
dune exec src/main.exe -- --self-test
dune exec src/main.exe -- --port 8080
```

ブラウザで <http://127.0.0.1:8080> を開きます。

## 対話モード

例題を選んで `Start interactive` を押すと、右側に現在のゴールと仮定が表示されます。
下の入力欄へタクティクを一つずつ入力し、`Run step` または Enter で進めます。
ゴールが 0 件になったら `qed.` で証明を完了します。不正な手はカーネルに拒否され、
証明履歴には追加されません。

## 論理式

ZFC の言語として、項は変数、原子論理式は `x = y` と `x in y`（または `x ∈ y`）です。

```text
not P              # ¬P
P and Q            # P ∧ Q
P or Q             # P ∨ Q
P -> Q             # P → Q
P <-> Q            # P ↔ Q
forall x, P        # ∀x, P
exists x, P        # ∃x, P
false              # ⊥
```

## 証明スクリプト

宣言とタクティクはすべて`.`で終わります。文中の改行は空白と同じなので、
論理式やタクティクの引数を複数行に分けられます。量化子の区切りには
`.`ではなく`,`を使います。

`(*`と`*)`で囲んだ部分はコメントです。コメントは複数行にでき、入れ子にも
できます。従来の`#`から行末までの行コメントも利用できます。

```text
(* Empty-set witness. This comment may contain periods. *)
Choose empty Hempty from empty_set. # A line comment
```

透明な命題の別名を`alias`で`theorem`より前に書けます。別名の後には0個以上の
引数を置けます。

```text
alias is_empty x :=
  forall y, not (y in x).
alias empty_alias x := is_empty x.

theorem alias_identity :
  forall a,
    (empty_alias a -> is_empty a).
intro a.
intro H.
exact H.
qed.
```

`alias`は証明済みの事実ではありません。検査前に本体へ展開されるため、
`exact is_empty`のように別名を証明として使うことはできません。
本体の自由変数は宣言した引数に限られ、適用時には変数捕獲を避けて同時に
代入されます。引数なしなら`alias foo := P.`と書きます。

存在量化された事実は`obtain`で具体化と存在除去を一度に行えます。

```text
obtain p Hp from pairing a b.
```

これは`pairing`を`a`, `b`で具体化し、freshな`p`と
`Hp : forall x, x in p <-> (x = a or x = b)`を現在の仮定へ追加します。
内部では`all_elim`と`ex_elim`のプリミティブ規則列として検査されます。

閉じた存在事実から証明全体で使う名前を選ぶ場合は、`theorem`より前に
`Choose`を書けます。

```text
alias is_empty x := forall y, not (y in x).
Choose empty Hempty from empty_set.

theorem chosen_empty_is_empty : is_empty empty.
exact Hempty.
qed.
```

`Choose`は、指定した存在命題の証明証明書を抽出カーネルで再検査してから、
新しいグローバル定数と、その定数で具体化した名前付き事実を環境へ追加します。
したがって、上の`empty`は以後の定理の主張にも現せます。同名の定数または
事実を再宣言することはできません。

全称量化子の後に存在量化子が続く事実からは、`Skolem`で関数記号を導入できます。
関数記号は`f(a,b)`のように項として書きます。

```text
Skolem pair Hpair from pairing.

theorem pair_shape :
  forall a, forall b, forall x,
    (x in pair(a,b) <-> (x = a or x = b)).
exact Hpair.
qed.
```

`Skolem f H from fact.` は、`fact`の証明書を再検査し、`forall ... exists ...`
の存在変数を`f`の適用で置き換えた名前付き事実をグローバル環境へ追加します。
導入された関数記号は以後の定理・タクティクで利用できます。

`qed.` の後に次の定理や宣言を続けることもできます。完了した定理は、後続の
宣言から名前で参照できるグローバル事実として証明書付きで登録されます。

```text
theorem and_commutes :
  forall x,
  forall y,
    ((x in y and y in x) -> (y in x and x in y)).
intro x.
intro y.
intro H.
split.
apply H.
apply H.
qed.
```

タクティクは `intro`, `assumption`, `exact`, `apply`, `specialize`, `obtain`, `refl`, `split`, `cases`,
`left`, `right`, `use`, `contradiction` を実装しています。`apply` は全称量化された
事実をゴールに合わせて具体化します。たとえば `apply extensionality` で外延性公理を
利用できます。仮定から新しい仮定を導く場合は、`apply H0 in H as H1` と書けます。
これは `H0` の一つの含意前提に `H` を適用し、結論を `H1` として追加します。

### プリミティブ推論規則

`rule x`でプリミティブな推論規則`x`を直接適用できます。例えば便利な
`intro`や`refl`を使わず、規則だけで反射律を証明できます。

```text
theorem equality_by_rules :
  forall x, x = x.
rule all_intro x.
rule equal_refl.
qed.
```

利用できる規則は次の18個です。

```text
axiom          hypothesis     falsum_elim
impl_intro     impl_elim
conj_intro     conj_elim_l    conj_elim_r
disj_intro_l   disj_intro_r   disj_elim
all_intro      all_elim
ex_intro       ex_elim
equal_refl     equal_elim
cut
```

`Cut`と等号除去も直接記述できます。

```text
rule cut H : P.
rule equal_elim s t x : P.
```

後者では`x`を述語`P`の置換位置として使い、現在のゴール`P[t/x]`を
`s = t`と`P[s/x]`の二つのゴールへ変換します。完全な例は
[examples/rules.zfp](examples/rules.zfp)にあります。

分出・置換の公理図式も`RAxiom`として直接適用できます。

```text
rule axiom separation a x : P.
rule axiom replacement a x y : P.
```

全称量化された仮定を明示的に具体化するには、次のように書きます。

```text
specialize H a as Hna.
contradiction.
```

複数の全称量化子は `specialize H a b as Hab` のように一度に具体化できます。

空集合公理は `empty_set` という名前で登録されています。

```text
theorem empty_set_exists :
  exists e, forall x, not (x in e).
exact empty_set.
qed.
```

分出・置換公理図式は、任意の論理式をカーネル内で安全に具体化します。

```text
separation S a x : not (x in x).
replacement R a x y : y = x.
```

## 信頼境界

OCaml層は構文解析と表面タクティクの規則列生成を行いますが、その結果による証明状態・
グローバル環境の変更はCoqから抽出されたカーネルだけが検査・実行します。
外延性・対・和・冪集合・無限・正則性・選択はカーネル公理として登録されています。
分出・置換は専用タクティクで公理図式のインスタンスを生成します。
外側のパーサー・HTTP・Web・VS Codeコードから抽出状態の表現やraw公理判定器へは
アクセスできません。
