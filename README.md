# ZFCert

一階述語論理と ZFC 集合論を対象とする、小さな OCaml 製定理証明支援系です。
証明スクリプトはサーバ側のカーネルで検査され、Web UI からすぐに試せます。

## Coqによる参照形式化

[coq/FOL.v](coq/FOL.v) に、一階述語論理と自然演繹を形式化しています。

- ZFCの項（de Bruijn indexによる変数）
- 等号、所属、論理結合子、全称・存在量化
- 捕獲を起こさないrenamingと量化子の具体化
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
確認します。抽出された`step`・`rule_run`は既存OCamlサーバーへ組み込まれており、
名前付き構文をde Bruijn形式へ変換した後、各タクティク遷移を抽出カーネルで検査します。
パーサー、名前解決、HTTP/UIは従来のOCamlコードが担当します。

抽出用エントリポイントは[coq/ExtractProofState.v](coq/ExtractProofState.v)に分離して
あります。既存アプリへはまだ接続しませんが、必要になった時点で次を実行できます。

```sh
make extract
```

生成物は`extracted/proof_state.ml`で、`step`, `run`, `rule_step`,
`rule_run`を含みます。単独のOCamlコンパイルも確認しています。

抽出された`Proof_state`モジュールはDuneのprivate moduleとして隠蔽されています。
外部へ公開するのは[extracted/zfcert_kernel.mli](extracted/zfcert_kernel.mli)だけで、
証明状態は構築子を持たない抽象型`Zfcert_kernel.state`です。初期状態は抽出された
`start`、以後の状態は抽出された`step`・`run`・`rule_step`・`rule_run`の返り値
としてのみ取得できます。

OCamlサーバーが保持する論理状態の正本もこの抽象`state`です。仮定名や表示用の
論理式は`display_goal`として別に保持しますが、各遷移後に抽出カーネルのgoal viewと
一致することを確認し、`qed`では抽出状態自身が空であることを検査します。
公理判定関数を外側から渡すAPIも公開せず、固定ZFC公理または分出・置換から作られた
抽象的な公理能力だけを`rule_run`へ渡します。

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

透明な命題定義を`theorem`より前に書けます。定義名の後には0個以上の
引数を置けます。

```text
Definition is_empty x :=
  forall y, not (y in x).
Definition empty_alias x := is_empty x.

theorem definition_identity :
  forall a,
    (empty_alias a -> is_empty a).
intro a.
intro H.
exact H.
qed.
```

定義は証明済みの事実ではなく、命題の別名です。検査前に本体へ展開されるため、
`exact is_empty`のように定義名を証明として使うことはできません。
定義本体の自由変数は宣言した引数に限られ、適用時には変数捕獲を避けて同時に
代入されます。引数なしの定義は`Definition foo := P.`と書きます。

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

タクティクは `intro`, `assumption`, `exact`, `apply`, `specialize`, `refl`, `split`, `cases`,
`left`, `right`, `use`, `contradiction` を実装しています。`apply` は全称量化された
事実をゴールに合わせて具体化します。たとえば `apply extensionality` で外延性公理を
利用できます。

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

構文解析、捕獲回避代入、α同値、自然演繹規則、公理の具体化を OCaml カーネルが検査します。
外延性・対・和・冪集合・無限・正則性・選択はカーネル公理として登録されています。
分出・置換は専用タクティクで公理図式のインスタンスを生成します。
外側のパーサー・HTTP・Web・VS Codeコードから抽出状態の表現やraw公理判定器へは
アクセスできません。
