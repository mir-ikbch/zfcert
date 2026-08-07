// Examples shown in the full proof-script editor on index.html.
const proofExamples = {
  identity: `theorem equality_reflexive : forall x, x = x.
intro x.
refl.
qed.`,
  implication: `theorem implication_identity : forall x, (x in x -> x in x).
intro x.
intro H.
exact H.
qed.`,
  conjunction: `theorem and_commutes :
  forall x,
  forall y, ((x in y and y in x) -> (y in x and x in y)).
intro x.
intro y.
intro H.
cases H H_yx H_xy.
split.
exact H_xy.
exact H_yx.
qed.`,
  extensionality: `theorem same_members_same_set :
  forall a,
  forall b, ((forall z, (z in a <-> z in b)) -> a = b).
intro a.
intro b.
intro H.
apply extensionality.
exact H.
qed.`,
  existence: `theorem self_exists : forall x, exists y, y = x.
intro x.
use x.
refl.
qed.`,
  obtain: `theorem obtain_witness :
  (exists x, x = x) -> exists y, y = y.
intro H.
obtain x Hx from H.
use x.
exact Hx.
qed.`,
  empty: `theorem empty_set_exists : exists e, forall x, not (x in e).
exact empty_set.
qed.`,
  separation: `theorem russell_subset_exists :
  forall a,
  exists b,
  forall x, (x in b <-> (x in a and not (x in x))).
intro a.
separation S a x : not (x in x).
exact S.
qed.`,
  alias: `alias is_empty x :=
  forall y, not (y in x).
theorem empty_identity : forall x, (is_empty x -> is_empty x).
intro x.
intro H.
exact H.
qed.`,
  choose: `alias is_empty x := forall y, not (y in x).
Choose empty Hempty from empty_set.
theorem chosen_empty_is_empty : is_empty empty.
put Hempty.
exact Hempty.
qed.`,
  choose_function: `Choose pair Hpair from pairing.
theorem pair_shape :
  forall a, forall b, forall x,
    (x in pair(a,b) <-> (x = a or x = b)).
put Hpair.
exact Hpair.
qed.`,
  rules: `theorem equality_by_rules :
  forall x, x = x.
rule all_intro x.
rule equal_refl.
  qed.`
};

// Lessons shown in tutorial.html. Keep this collection independent from
// [proofExamples] so the two pages can evolve separately.
const tutorialExamples = {
  identity: `theorem equality_reflexive : forall x, x = x.
intro x.
refl.
qed.`,
  implication: `theorem implication_identity : forall x, (x in x -> x in x).
intro x.
intro H.
exact H.
qed.`,
  conjunction: `theorem and_commutes :
  forall x,
  forall y, ((x in y and y in x) -> (y in x and x in y)).
intro x.
intro y.
intro H.
cases H H_yx H_xy.
split.
exact H_xy.
exact H_yx.
qed.`,
  extensionality: `theorem same_members_same_set :
  forall a,
  forall b, ((forall z, (z in a <-> z in b)) -> a = b).
intro a.
intro b.
intro H.
apply extensionality.
exact H.
qed.`,
  existence: `theorem self_exists : forall x, exists y, y = x.
intro x.
use x.
refl.
qed.`,
  obtain: `theorem obtain_witness :
  (exists x, x = x) -> exists y, y = y.
intro H.
obtain x Hx from H.
use x.
exact Hx.
qed.`,
  empty: `theorem empty_set_exists : exists e, forall x, not (x in e).
exact empty_set.
qed.`,
  separation: `theorem russell_subset_exists :
  forall a,
  exists b,
  forall x, (x in b <-> (x in a and not (x in x))).
intro a.
separation S a x : not (x in x).
exact S.
qed.`,
  alias: `alias is_empty x :=
  forall y, not (y in x).
theorem empty_identity : forall x, (is_empty x -> is_empty x).
intro x.
intro H.
exact H.
qed.`,
  choose: `alias is_empty x := forall y, not (y in x).
Choose empty Hempty from empty_set.
theorem chosen_empty_is_empty : is_empty empty.
put Hempty.
exact Hempty.
qed.`,
  choose_function: `Choose pair Hpair from pairing.
theorem pair_shape :
  forall a, forall b, forall x,
    (x in pair(a,b) <-> (x = a or x = b)).
put Hpair.
exact Hpair.
qed.`,
  rules: `theorem equality_by_rules :
  forall x, x = x.
rule all_intro x.
rule equal_refl.
qed.`
};

const tutorialExplanations = {
  identity: {
    title: "Equality reflexivity",
    html: `<p>Every object is equal to itself. The goal begins with a universal quantifier, so first introduce an arbitrary object.</p>
      <ol><li>Use <code>intro x.</code> to name the object.</li><li>Use <code>refl.</code> when the goal has the form <code>t = t</code>.</li></ol>
      <p class="tutorial-tip">Try the two tactics in order, then finish with <code>qed.</code>.</p>`
  },
  implication: {
    title: "Implication identity",
    html: `<p>To prove an implication, assume its left-hand side. The assumption then gives exactly the goal you need.</p>
      <ol><li>Introduce <code>x</code>.</li><li>Introduce the implication hypothesis.</li><li>Close the goal with <code>exact H.</code>.</li></ol>`
  },
  conjunction: {
    title: "Conjunction commutativity",
    html: `<p>A conjunction stores two facts in one hypothesis. Take it apart, then build a new conjunction in the opposite order.</p>
      <ol><li>Introduce the variables and hypothesis.</li><li>Use <code>cases</code> to name both parts.</li><li>Use <code>split.</code> and solve the two goals.</li></ol>`
  },
  extensionality: {
    title: "Using extensionality",
    html: `<p>Two sets are equal when they have the same members. This proof applies the extensionality axiom to the membership equivalence already given.</p>
      <ol><li>Introduce <code>a</code>, <code>b</code>, and the membership hypothesis.</li><li>Use <code>apply extensionality.</code>.</li><li>Pass the hypothesis with <code>exact H.</code>.</li></ol>`
  },
  existence: {
    title: "Existential witness",
    html: `<p>To prove that something exists, choose a concrete witness. Here the object introduced at the start is the natural witness.</p>
      <ol><li>Introduce <code>x</code>.</li><li>Choose it with <code>use x.</code>.</li><li>Prove the remaining equality by reflexivity.</li></ol>`
  },
  obtain: {
    title: "Obtain from existence",
    html: `<p>An existential hypothesis hides a witness. The <code>obtain</code> tactic brings that witness and its property into the context.</p>
      <ol><li>Introduce the existential hypothesis.</li><li>Use <code>obtain x Hx from H.</code>.</li><li>Reuse <code>x</code> as the new witness.</li></ol>`
  },
  empty: {
    title: "The empty set",
    html: `<p>The empty-set axiom already proves the theorem we want: there is a set with no members.</p>
      <p>Use the named fact <code>empty_set</code> directly. The kernel checks that its statement matches the current goal.</p>`
  },
  separation: {
    title: "Separation schema",
    html: `<p>Separation creates a subset by keeping exactly the members that satisfy a predicate. This example removes the sets that contain themselves.</p>
      <ol><li>Introduce the source set.</li><li>Instantiate the schema with <code>separation</code>.</li><li>Use the generated fact to close the existential goal.</li></ol>`
  },
  alias: {
    title: "Proposition aliases",
    html: `<p>An alias gives a reusable name to a proposition. After the alias declaration, the theorem can use that name just like its expanded formula.</p>
      <ol><li>Introduce the object.</li><li>Assume the aliased proposition.</li><li>Return the same assumption.</li></ol>`
  },
  choose: {
    title: "Choose a named witness",
    html: `<p><code>Choose</code> names a certified witness from an existential fact. The chosen fact stays hidden until you explicitly put it into the proof context.</p>
      <ol><li>Use <code>put Hempty.</code> to reveal the fact.</li><li>Finish with <code>exact Hempty.</code>.</li></ol>`
  },
  choose_function: {
    title: "Choose a function",
    html: `<p>Some axioms provide a function-like witness. <code>Choose</code> records that witness and its certified property for later proofs.</p>
      <ol><li>Put the named fact into the context.</li><li>Use the fact to prove the shape of the chosen function.</li></ol>`
  },
  rules: {
    title: "Primitive rules only",
    html: `<p>This lesson exposes the underlying natural-deduction rules directly instead of using the friendly tactic names.</p>
      <ol><li>Use <code>all_intro</code> to introduce the universal variable.</li><li>Use <code>equal_refl</code> to close the equality goal.</li></ol>`
  }
};

const isJapanese = document.documentElement.lang === "ja";

const tutorialExplanationsJa = {
  identity: {
    title: "等号の反射律",
    html: `<p>すべての対象は自分自身と等しくなります。ゴールは全称量化から始まるので、まず任意の対象を導入します。</p>
      <ol><li><code>intro x.</code> で対象に名前を付けます。</li><li>ゴールが <code>t = t</code> の形になったら <code>refl.</code> を使います。</li></ol>
      <p class="tutorial-tip">2つのタクティクを順番に試し、最後に <code>qed.</code> で完了します。</p>`
  },
  implication: {
    title: "含意の恒等性",
    html: `<p>含意を証明するには、左辺を仮定します。その仮定が、そのまま必要なゴールになります。</p>
      <ol><li><code>x</code> を導入します。</li><li>含意の仮定を導入します。</li><li><code>exact H.</code> でゴールを閉じます。</li></ol>`
  },
  conjunction: {
    title: "連言の交換",
    html: `<p>連言の仮定には2つの事実が入っています。それを取り出し、順番を入れ替えた連言を作ります。</p>
      <ol><li>変数と仮定を導入します。</li><li><code>cases</code> で2つの部分に名前を付けます。</li><li><code>split.</code> で2つのゴールを作り、それぞれを解きます。</li></ol>`
  },
  extensionality: {
    title: "外延性の利用",
    html: `<p>同じ元を持つ2つの集合は等しくなります。この証明では、与えられた元の同値を外延性公理に渡します。</p>
      <ol><li><code>a</code>、<code>b</code>、元についての仮定を導入します。</li><li><code>apply extensionality.</code> を使います。</li><li><code>exact H.</code> で仮定を渡します。</li></ol>`
  },
  existence: {
    title: "存在の証人",
    html: `<p>何かが存在することを証明するには、具体的な証人を選びます。ここでは最初に導入した対象が自然な証人です。</p>
      <ol><li><code>x</code> を導入します。</li><li><code>use x.</code> で証人に選びます。</li><li>残った等号を反射律で証明します。</li></ol>`
  },
  obtain: {
    title: "存在からの取り出し",
    html: `<p>存在量化された仮定には証人が隠れています。<code>obtain</code> タクティクで、その証人と性質をコンテキストに取り出します。</p>
      <ol><li>存在量化された仮定を導入します。</li><li><code>obtain x Hx from H.</code> を使います。</li><li><code>x</code> を新しい証人として再利用します。</li></ol>`
  },
  empty: {
    title: "空集合",
    html: `<p>空集合公理は、元を持たない集合が存在することをすでに証明しています。</p>
      <p>名前付きの事実 <code>empty_set</code> を直接使います。カーネルが現在のゴールとの一致を確認します。</p>`
  },
  separation: {
    title: "分出公理図式",
    html: `<p>分出は、述語を満たす元だけを残して部分集合を作ります。この例では、自分自身を含む集合を取り除きます。</p>
      <ol><li>元の集合を導入します。</li><li><code>separation</code> で公理図式を具体化します。</li><li>生成された事実で存在ゴールを閉じます。</li></ol>`
  },
  alias: {
    title: "命題エイリアス",
    html: `<p>エイリアスを使うと、命題に再利用可能な名前を付けられます。宣言後は、展開後の式と同じようにその名前を使えます。</p>
      <ol><li>対象を導入します。</li><li>エイリアスで表された命題を仮定します。</li><li>同じ仮定を返します。</li></ol>`
  },
  choose: {
    title: "名前付き証人の選択",
    html: `<p><code>Choose</code> は存在量化された事実から、証明済みの証人に名前を付けます。その事実は、明示的にコンテキストへ入れるまで隠されています。</p>
      <ol><li><code>put Hempty.</code> で事実を表示します。</li><li><code>exact Hempty.</code> で終了します。</li></ol>`
  },
  choose_function: {
    title: "関数の選択",
    html: `<p>公理によっては関数のような証人が得られます。<code>Choose</code> は、その証人と証明済みの性質を後の証明のために記録します。</p>
      <ol><li>名前付きの事実をコンテキストへ入れます。</li><li>その事実を使って、選ばれた関数の形を証明します。</li></ol>`
  },
  rules: {
    title: "基本規則だけを使う",
    html: `<p>このレッスンでは、親しみやすいタクティク名の代わりに、自然演繹の基本規則を直接使います。</p>
      <ol><li><code>all_intro</code> で全称変数を導入します。</li><li><code>equal_refl</code> で等号ゴールを閉じます。</li></ol>`
  }
};

const ui = isJapanese ? {
  notStarted: "未開始",
  startInteractive: "↓で定理宣言から開始します。",
  checkedRules: count => `検証済みの基本規則を表示 (${count})`,
  constant: "定数",
  declarationSummary: (aliases, constants) => `${aliases} 個のエイリアス · ${constants} 個の定数`,
  current: "現在: ",
  checking: "確認中…",
  verify: "証明を検証",
  declarationsLoaded: "宣言を読み込みました",
  globalDeclarationsLoaded: "グローバル宣言を読み込みました",
  verified: steps => `検証済み · ${steps} ステップ`,
  rejected: line => `拒否 · ${line} 行目`,
  proofRejected: "証明を検証できませんでした",
  stepRejected: "ステップが拒否されました",
  connectionError: "接続エラー",
  kernelUnavailable: "カーネルに接続できません",
  interactive: steps => `対話中 · ${steps} ステップ`,
  goalsSolved: "ゴールを解決しました",
  proofComplete: "証明完了",
  allGoalsSolved: "すべてのゴールを解決しました",
  addQed: "証明を完了するには qed. を追加してください。",
  goal: count => `${count} ゴール`,
  goals: count => `${count} ゴール`,
  variables: "変数",
  noAssumptions: "仮定なし",
  declarationsChecked: "宣言を確認しました。定理を記述できます。",
  enterTactic: "現在のゴールに対するタクティクを入力してください。",
  proofVerified: "証明は抽出カーネルによって検証されました。",
  proofCompleteKernel: "証明が完了し、抽出カーネルによって検証されました。",
  tutorialStateUnavailable: "証明状態を利用できません。",
  theoremReady: "定理宣言の準備ができました。",
  noOpenGoals: "未解決のゴールはありません。",
  initialGoal: "初期ゴール",
  afterTactic: index => `タクティク ${index} の後`,
  tutorialReady: "最初のタクティクを入力できます。",
  tacticCount: count => `${count} タクティク`,
  stateCount: count => `${count} 状態`,
  oneState: "1 状態",
  emptyTutorialScript: "例題を選択してください。",
  preparing: "証明状態を準備中…",
  noTheorem: "定理が選択されていません",
  noTheoremFound: "完全な定理宣言が見つかりません。",
  theoremLoadFailed: "定理を読み込めませんでした",
  tutorialStartError: "チュートリアルを開始するには、完全な定理宣言が必要です。",
  enterOneTactic: "1つのタクティクを入力してください。例: intro x.",
  oneLineTactic: "タクティクは1行で入力してください。",
  checkingTactic: "タクティクを確認中…",
  tacticAccepted: "タクティクを受け付けました。",
  tutorialProofComplete: "証明完了。",
  selectedScheme: "(図式)"
} : {
  notStarted: "Not started",
  startInteractive: "Press ↓ to begin at the theorem declaration.",
  checkedRules: count => `Show checked primitive rules (${count})`,
  constant: "constant",
  declarationSummary: (aliases, constants) => `${aliases} aliases · ${constants} constants`,
  current: "Current: ",
  checking: "Checking…",
  verify: "Verify proof",
  declarationsLoaded: "Global declarations loaded",
  globalDeclarationsLoaded: "Global declarations loaded",
  verified: steps => `VERIFIED · ${steps} STEPS`,
  rejected: line => `REJECTED · LINE ${line}`,
  proofRejected: "The proof could not be verified",
  stepRejected: "The step was rejected",
  connectionError: "CONNECTION ERROR",
  kernelUnavailable: "Cannot connect to the kernel",
  interactive: steps => `INTERACTIVE · ${steps} STEPS`,
  goalsSolved: "GOALS SOLVED",
  proofComplete: "Proof complete",
  allGoalsSolved: "All goals solved",
  addQed: "Run qed. to finish the proof.",
  goal: count => `${count} goal${count === 1 ? "" : "s"}`,
  goals: count => `${count} goal${count === 1 ? "" : "s"}`,
  variables: "Variables",
  noAssumptions: "No assumptions",
  declarationsChecked: "Declarations checked. You can now write a theorem.",
  enterTactic: "Enter a tactic for the current goal.",
  proofVerified: "The proof was verified by the extracted kernel.",
  proofCompleteKernel: "The proof is complete and was verified by the extracted kernel.",
  tutorialStateUnavailable: "The proof state is unavailable.",
  theoremReady: "The theorem declaration is ready.",
  noOpenGoals: "No open goals.",
  initialGoal: "Initial goal",
  afterTactic: index => `After tactic ${index}`,
  tutorialReady: "The theorem is ready for its first tactic.",
  tacticCount: count => `${count} tactic${count === 1 ? "" : "s"}`,
  stateCount: count => `${count} states`,
  oneState: "1 state",
  emptyTutorialScript: "Select an example or write a theorem in the script editor below.",
  preparing: "Preparing proof state…",
  noTheorem: "No theorem selected",
  noTheoremFound: "No complete theorem declaration was found.",
  theoremLoadFailed: "The theorem could not be loaded",
  tutorialStartError: "A complete theorem declaration is needed to start the tutorial.",
  enterOneTactic: "Enter one tactic, such as intro x.",
  oneLineTactic: "Enter one tactic on a single line.",
  checkingTactic: "Checking tactic…",
  tacticAccepted: "Tactic accepted.",
  tutorialProofComplete: "Proof complete.",
  selectedScheme: "(scheme)"
};

const axiomNotesJa = {
  empty_set: "元を持たない集合が存在します。",
  extensionality: "同じ元を持つ集合は等しくなります。",
  pairing: "任意の2つの集合から対集合を作れます。",
  union: "任意の集合には和集合があります。",
  power_set: "任意の集合には冪集合があります。",
  infinity: "帰納的な集合が存在します。",
  foundation: "空でない集合には、互いに素な元があります。",
  separation: "P は任意の論理式にできます。この項目は図式のテンプレートです。",
  replacement: "関数を定める各論理式に対する図式のインスタンスです。",
  choice: "空でない集合族ごとに選択集合が存在します。"
};

const editor = document.querySelector("#proof-editor");
const numbers = document.querySelector("#line-numbers");
const result = document.querySelector("#result");
const verifyButton = document.querySelector("#verify-button");
const exampleSelect = document.querySelector("#example-select");
const tutorialExampleSelect = document.querySelector("#tutorial-example-select");
const goalView = document.querySelector("#goal-view");
const goalCount = document.querySelector("#goal-count");
const editorMarker = document.querySelector("#editor-marker");
const previousStepButton = document.querySelector("#previous-step-button");
const nextStepButton = document.querySelector("#next-step-button");
const stepIndicator = document.querySelector("#step-indicator");
const tutorialTheorem = document.querySelector("#tutorial-theorem");
const tutorialScript = document.querySelector("#tutorial-script");
const tutorialInput = document.querySelector("#tutorial-input");
const tutorialApplyButton = document.querySelector("#tutorial-apply-button");
const tutorialResetButton = document.querySelector("#tutorial-reset-button");
const tutorialMessage = document.querySelector("#tutorial-message");
const tutorialExplanationTitle = document.querySelector("#tutorial-explanation-title");
const tutorialExplanation = document.querySelector("#tutorial-explanation");
const tutorialHistory = document.querySelector("#tutorial-history");
const tutorialStepCount = document.querySelector("#tutorial-step-count");
const tutorialHistoryCount = document.querySelector("#tutorial-history-count");
let interactiveCursor = -1;
let interactiveCheckpoints = [];
let interactiveRange;
let interactiveBusy = false;
let tutorialBaseScript = "";
let tutorialCommands = [];
let tutorialStates = [];
let tutorialBusy = false;
let tutorialRevision = 0;
let tutorialResetTimer;
let wasmApiPromise;

function wasmApi() {
  if (wasmApiPromise) return wasmApiPromise;

  wasmApiPromise = new Promise((resolve, reject) => {
    const startedAt = Date.now();
    const fallbackAfterMs = 1500;
    const timeoutMs = 10000;
    const poll = () => {
      if (window.ZfcertWasm) {
        resolve(window.ZfcertWasm);
        return;
      }
      if (window.ZfcertJs && Date.now() - startedAt >= fallbackAfterMs) {
        resolve(window.ZfcertJs);
        return;
      }
      if (Date.now() - startedAt >= timeoutMs) {
        reject(new Error("The browser kernel did not finish loading."));
        return;
      }
      window.setTimeout(poll, 20);
    };
    poll();
  });

  return wasmApiPromise;
}

function currentLineRange(text, start, end) {
  const segment = text.slice(start, end);
  const firstContent = segment.search(/\S/);
  const firstOffset = firstContent < 0 ? start : start + firstContent;
  const lastOffset = Math.max(firstOffset, end - 1);
  return {
    start: text.slice(0, firstOffset).split("\n").length,
    end: text.slice(0, lastOffset).split("\n").length
  };
}

function updateEditorMarker() {
  if (!interactiveRange) {
    editorMarker.style.opacity = "0";
    return;
  }
  const computed = window.getComputedStyle(editor);
  const lineHeight = parseFloat(computed.lineHeight);
  const paddingTop = parseFloat(computed.paddingTop);
  const top = paddingTop + (interactiveRange.start - 1) * lineHeight - editor.scrollTop;
  const height = Math.max(1, interactiveRange.end - interactiveRange.start + 1) * lineHeight;
  editorMarker.style.top = `${top}px`;
  editorMarker.style.height = `${height}px`;
  editorMarker.style.opacity = "1";
}

function updateLineNumbers() {
  const count = editor.value.split("\n").length;
  numbers.innerHTML = Array.from({ length: count }, (_, i) => {
    const line = i + 1;
    const active = interactiveRange &&
      line >= interactiveRange.start && line <= interactiveRange.end;
    return `<span class="${active ? "active" : ""}">${line}</span>`;
  }).join("");
  numbers.scrollTop = editor.scrollTop;
  updateEditorMarker();
}

function resetInteractive() {
  interactiveCursor = -1;
  interactiveCheckpoints = proofCheckpoints(editor.value);
  interactiveRange = undefined;
  goalCount.textContent = ui.notStarted;
  stepIndicator.textContent = ui.notStarted;
  goalView.innerHTML = `<p>${ui.startInteractive}</p>`;
  updateLineNumbers();
  updateNavigationControls();
}

function setExample(name) {
  editor.value = proofExamples[name];
  resetInteractive();
}

function escapeHtml(value) {
  return String(value)
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;");
}

function certificateHtml(rules) {
  if (!Array.isArray(rules) || rules.length === 0) return "";
  return `
    <details class="certificate">
      <summary>${ui.checkedRules(rules.length)}</summary>
      <ol>${rules.map((rule) =>
        `<li><code>${escapeHtml(rule)}</code></li>`
      ).join("")}</ol>
    </details>`;
}

function declarationsHtml(data) {
  const aliases = (data.aliases || []).map((alias) =>
    `<code>${escapeHtml(
      [alias.name, ...(alias.parameters || [])].join(" ")
    )}</code> := ${escapeHtml(alias.statement)}`
  );
  const constants = (data.constants || []).map((name) =>
    `<code>${escapeHtml(name)}</code> (${ui.constant})`
  );
  const facts = (data.facts || []).map((fact) =>
    `<code>${escapeHtml(fact.name)}</code> : ${escapeHtml(fact.formula)}`
  );
  return [...aliases, ...constants, ...facts].join("<br>");
}

function declarationSummary(data) {
  return ui.declarationSummary(
    (data.aliases || []).length,
    (data.constants || []).length
  );
}

function currentCommandHtml() {
  const checkpoint = interactiveCheckpoints[interactiveCursor];
  if (!checkpoint) return "";
  return `<span class="step-command">${ui.current}${escapeHtml(checkpoint.label)}</span>`;
}

async function verify() {
  verifyButton.disabled = true;
  verifyButton.querySelector("span").textContent = ui.checking;
  try {
    const api = await wasmApi();
    const data = JSON.parse(api.check(editor.value));
    if (data.ok && data.aliasesOnly) {
      result.className = "result success";
      result.innerHTML = `
        <div class="result-icon">✓</div>
        <p class="result-kicker">${escapeHtml(declarationSummary(data))}</p>
        <h3>${ui.globalDeclarationsLoaded}</h3>
        <p>${declarationsHtml(data)}</p>`;
    } else if (data.ok) {
      result.className = "result success";
      result.innerHTML = `
        <div class="result-icon">✓</div>
        <p class="result-kicker">${ui.verified(data.steps)}</p>
        <h3>${escapeHtml(data.theorem)}</h3>
        <p><code>${escapeHtml(data.statement)}</code><br>${ui.proofVerified}</p>
        ${certificateHtml(data.certificate)}`;
    } else {
      result.className = "result error";
      result.innerHTML = `
        <div class="result-icon">!</div>
        <p class="result-kicker">${ui.rejected(data.line)}</p>
        <h3>${ui.proofRejected}</h3>
        <p>${escapeHtml(data.message)}</p>`;
    }
  } catch (error) {
    result.className = "result error";
    result.innerHTML = `
      <div class="result-icon">!</div>
        <p class="result-kicker">${ui.connectionError}</p>
        <h3>${ui.kernelUnavailable}</h3>
      <p>${escapeHtml(error.message)}</p>`;
  } finally {
    verifyButton.disabled = false;
    verifyButton.querySelector("span").textContent = ui.verify;
  }
}

function renderInteractive(data) {
  if (!data.ok) {
    goalCount.textContent = ui.stepRejected;
    goalView.innerHTML = `<p>${escapeHtml(data.message)}</p>`;
    result.className = "result error";
    result.innerHTML = `
      <div class="result-icon">!</div>
      <p class="result-kicker">${ui.rejected(data.line)}</p>
      <h3>${ui.stepRejected}</h3>
      <p>${escapeHtml(data.message)}</p>`;
    return;
  }

  if (data.aliasesOnly) {
    goalCount.textContent = declarationSummary(data);
    goalView.innerHTML = `${declarationsHtml(data)}${currentCommandHtml()}`;
    result.className = "result success";
    result.innerHTML = `
      <div class="result-icon">✓</div>
      <p class="result-kicker">${ui.declarationsLoaded}</p>
      <p>${ui.declarationsChecked}</p>`;
    return;
  }

  if (data.qed) {
    goalCount.textContent = ui.proofComplete;
    goalView.innerHTML = `
      <span class="goal-target">✓ ${escapeHtml(data.statement)}</span>
      ${currentCommandHtml()}`;
    result.className = "result success";
    result.innerHTML = `
      <div class="result-icon">✓</div>
      <p class="result-kicker">${ui.verified(data.steps)}</p>
      <h3>${escapeHtml(data.theorem)}</h3>
      <p>${ui.proofCompleteKernel}</p>
      ${certificateHtml(data.certificate)}`;
    return;
  }

  result.className = "result active";
  result.innerHTML = `
    <div class="result-icon">${data.complete ? "✓" : "→"}</div>
    <p class="result-kicker">${data.complete ? ui.goalsSolved : ui.interactive(data.steps)}</p>
    <h3>${escapeHtml(data.theorem)}</h3>
    <p>${data.complete ? ui.allGoalsSolved : ui.enterTactic}</p>`;

  if (data.complete) {
    goalCount.textContent = ui.goals(0);
    goalView.innerHTML = `
      <span class="goal-target">${ui.allGoalsSolved}</span>
      <p>${ui.addQed}</p>
      ${currentCommandHtml()}`;
    return;
  }

  const goal = data.goals[0];
  goalCount.textContent = ui.goal(data.goals.length);
  const variables = Array.isArray(goal.variables) && goal.variables.length
    ? `<div class="goal-variables"><strong>${ui.variables}</strong>:
        ${goal.variables.map((name) => escapeHtml(name)).join(", ")}</div>`
    : "";
  const context = goal.context.length
    ? `<ul class="goal-context">${goal.context.map((entry) =>
        `<li><strong>${escapeHtml(entry.name)}</strong> : ${escapeHtml(entry.formula)}</li>`
      ).join("")}</ul>`
    : `<p class="goal-context">${ui.noAssumptions}</p>`;
  goalView.innerHTML = `
    ${variables}
    ${context}
    <span class="goal-target">⊢ ${escapeHtml(goal.target)}</span>
    ${currentCommandHtml()}`;
}

async function inspectInteractive(script) {
  const api = await wasmApi();
  return JSON.parse(api.step(script));
}

function renderTutorialExplanation() {
  if (!tutorialExplanation || !tutorialExplanationTitle) return;
  const explanations = isJapanese ? tutorialExplanationsJa : tutorialExplanations;
  const lesson = explanations[tutorialExampleSelect?.value || "identity"]
    || explanations.identity;
  tutorialExplanationTitle.textContent = lesson.title;
  tutorialExplanation.innerHTML = lesson.html;
}

function tutorialSource() {
  const sourceText = editor
    ? editor.value
    : tutorialExamples[tutorialExampleSelect?.value || "identity"];
  if (!sourceText) return undefined;
  const checkpoints = proofCheckpoints(sourceText);
  if (checkpoints.length === 0) return undefined;
  return sourceText.slice(0, checkpoints[0].end);
}

function setTutorialMessage(kind, message) {
  tutorialMessage.className = `tutorial-message${kind ? ` ${kind}` : ""}`;
  tutorialMessage.textContent = message;
}

function tutorialStateHtml(data) {
  if (!data || !data.ok) {
    return `<p class="tutorial-state-error">${escapeHtml(data?.message || ui.tutorialStateUnavailable)}</p>`;
  }

  if (data.aliasesOnly) {
    return `<p class="tutorial-state-note">${ui.theoremReady}</p>`;
  }

  if (data.qed) {
    return `
      <div class="tutorial-complete">✓ ${ui.proofComplete}</div>
      <p class="tutorial-state-note">${ui.proofCompleteKernel}</p>`;
  }

  if (data.complete) {
    return `
      <div class="tutorial-complete">✓ ${ui.allGoalsSolved}</div>
      <p class="tutorial-state-note">${ui.addQed}</p>`;
  }

  const goals = Array.isArray(data.goals) ? data.goals : [];
  if (goals.length === 0) {
    return `<p class="tutorial-state-note">${ui.noOpenGoals}</p>`;
  }

  return goals.map((goal, index) => {
    const variables = Array.isArray(goal.variables) && goal.variables.length
      ? `<div class="tutorial-variables"><strong>${ui.variables}</strong>:
          ${goal.variables.map((name) => escapeHtml(name)).join(", ")}</div>`
      : "";
    const context = Array.isArray(goal.context) && goal.context.length
      ? `<ul class="tutorial-context">${goal.context.map((entry) =>
          `<li><strong>${escapeHtml(entry.name)}</strong> : ${escapeHtml(entry.formula)}</li>`
        ).join("")}</ul>`
      : `<p class="tutorial-no-context">${ui.noAssumptions}</p>`;
    return `
      <div class="tutorial-goal">
        <span class="tutorial-goal-label">${isJapanese ? "ゴール" : "Goal"} ${index + 1}</span>
        ${variables}
        ${context}
        <span class="tutorial-goal-target">⊢ ${escapeHtml(goal.target)}</span>
      </div>`;
  }).join("");
}

function renderTutorialScript() {
  const baseLines = tutorialBaseScript
    ? tutorialBaseScript.trimEnd().split("\n")
    : [];
  const baseRows = baseLines.map((line, index) => `
    <div class="tutorial-script-line tutorial-script-fixed">
      <span>${index + 1}</span>
      <code>${escapeHtml(line || " ")}</code>
    </div>`).join("");
  const commandRows = tutorialCommands.map((command, index) => `
    <div class="tutorial-script-line tutorial-script-command">
      <span>${baseLines.length + index + 1}</span>
      <code>${escapeHtml(command)}</code>
    </div>`).join("");

  tutorialScript.innerHTML = baseRows + commandRows ||
    `<p class="tutorial-empty-script">${ui.emptyTutorialScript}</p>`;
  tutorialStepCount.textContent = ui.tacticCount(tutorialCommands.length);
}

function renderTutorialHistory() {
  tutorialHistoryCount.textContent = tutorialStates.length === 1
    ? ui.oneState
    : ui.stateCount(tutorialStates.length);
  if (tutorialStates.length === 0) {
    tutorialHistory.innerHTML = `<div class="tutorial-history-empty">${ui.tutorialReady}</div>`;
    return;
  }

  const lastIndex = tutorialStates.length - 1;
  tutorialHistory.innerHTML = tutorialStates.map((entry, index) => `
    <article class="tutorial-state${index === lastIndex ? " current" : ""}">
      <div class="tutorial-state-head">
        <span>${index === 0 ? ui.initialGoal : ui.afterTactic(index)}</span>
        <span>${index + 1}/${tutorialStates.length}</span>
      </div>
      ${entry.command
        ? `<code class="tutorial-state-command">${escapeHtml(entry.command)}</code>`
        : `<p class="tutorial-state-note tutorial-state-start">${ui.tutorialReady}</p>`}
      <div class="tutorial-state-body">${tutorialStateHtml(entry.data)}</div>
    </article>`).join("");
  const current = tutorialHistory.querySelector(".tutorial-state.current");
  current?.scrollIntoView({ block: "nearest" });
}

function setTutorialAvailability() {
  const last = tutorialStates[tutorialStates.length - 1];
  const finished = last?.data?.qed === true;
  tutorialInput.disabled = tutorialBusy || finished || tutorialBaseScript === "";
  tutorialApplyButton.disabled = tutorialBusy || finished || tutorialBaseScript === "";
  tutorialResetButton.disabled = tutorialBusy;
}

function renderTutorial() {
  renderTutorialScript();
  renderTutorialHistory();
  setTutorialAvailability();
}

async function resetTutorial() {
  const revision = ++tutorialRevision;
  tutorialBusy = false;
  tutorialCommands = [];
  tutorialStates = [];
  renderTutorialExplanation();
  tutorialBaseScript = tutorialSource() || "";
  tutorialTheorem.textContent = tutorialBaseScript
    ? ui.preparing
    : ui.noTheorem;
  setTutorialMessage("", "");
  renderTutorial();

  if (!tutorialBaseScript) {
    setTutorialMessage("error", ui.tutorialStartError);
    return;
  }

  tutorialBusy = true;
  setTutorialAvailability();
  try {
    const data = await inspectInteractive(tutorialBaseScript);
    if (revision !== tutorialRevision) return;
    if (!data.ok) {
      tutorialTheorem.textContent = ui.theoremLoadFailed;
      setTutorialMessage("error", data.message);
      tutorialHistory.innerHTML = `<div class="tutorial-history-empty tutorial-history-error">${escapeHtml(data.message)}</div>`;
      return;
    }
    tutorialTheorem.textContent = `${data.theorem} : ${data.statement}`;
    tutorialStates = [{ command: "", data }];
    renderTutorial();
  } catch (error) {
    if (revision !== tutorialRevision) return;
    tutorialTheorem.textContent = ui.theoremLoadFailed;
    setTutorialMessage("error", error.message);
    tutorialHistory.innerHTML = `<div class="tutorial-history-empty tutorial-history-error">${escapeHtml(error.message)}</div>`;
  } finally {
    if (revision === tutorialRevision) {
      tutorialBusy = false;
      setTutorialAvailability();
    }
  }
}

async function applyTutorialTactic() {
  if (tutorialBusy) return;
  if (!tutorialBaseScript) {
    setTutorialMessage("error", ui.tutorialStartError);
    return;
  }

  const raw = tutorialInput.value.trim();
  if (raw === "") {
    setTutorialMessage("error", ui.enterOneTactic);
    tutorialInput.focus();
    return;
  }
  if (raw.includes("\n")) {
    setTutorialMessage("error", ui.oneLineTactic);
    return;
  }

  const command = raw.endsWith(".") ? raw : `${raw}.`;
  const revision = tutorialRevision;
  const script = [tutorialBaseScript, ...tutorialCommands, command].join("\n");
  tutorialBusy = true;
  setTutorialMessage("", ui.checkingTactic);
  setTutorialAvailability();
  try {
    const data = await inspectInteractive(script);
    if (revision !== tutorialRevision) return;
    if (!data.ok) {
      setTutorialMessage("error", `Line ${data.line}: ${data.message}`);
      return;
    }
    tutorialCommands = [...tutorialCommands, command];
    tutorialStates = [...tutorialStates, { command, data }];
    tutorialInput.value = "";
    setTutorialMessage("accepted", data.qed ? ui.tutorialProofComplete : ui.tacticAccepted);
    renderTutorial();
    tutorialInput.focus();
  } catch (error) {
    if (revision === tutorialRevision) setTutorialMessage("error", error.message);
  } finally {
    if (revision === tutorialRevision) {
      tutorialBusy = false;
      setTutorialAvailability();
    }
  }
}

function scheduleTutorialReset() {
  window.clearTimeout(tutorialResetTimer);
  tutorialResetTimer = window.setTimeout(() => resetTutorial(), 180);
}

function theoremPrefixEnd(text) {
  let statement = "";
  let lineComment = false;
  let blockDepth = 0;
  for (let index = 0; index < text.length; index += 1) {
    const character = text[index];
    if (blockDepth > 0) {
      if (text.startsWith("(*", index)) {
        blockDepth += 1;
        index += 1;
      } else if (text.startsWith("*)", index)) {
        blockDepth -= 1;
        index += 1;
      } else if (character === "\n") {
        statement += " ";
      }
      continue;
    }
    if (lineComment) {
      if (character === "\n") {
        lineComment = false;
        statement += " ";
      }
      continue;
    }
    if (text.startsWith("(*", index)) {
      blockDepth = 1;
      statement += " ";
      index += 1;
    } else if (character === "#") {
      lineComment = true;
    } else if (character === ".") {
      if (statement.trim().toLowerCase().startsWith("theorem ")) {
        return index + 1;
      }
      statement = "";
    } else {
      statement += character === "\n" ? " " : character;
    }
  }
  return undefined;
}

function proofCheckpoints(text) {
  const theoremEnd = theoremPrefixEnd(text);
  if (theoremEnd === undefined) return [];

  const checkpoints = [{
    start: 0,
    end: theoremEnd,
    range: currentLineRange(text, 0, theoremEnd),
    label: "theorem declaration"
  }];
  let statementStart = theoremEnd;
  let lineComment = false;
  let blockDepth = 0;

  for (let index = theoremEnd; index < text.length; index += 1) {
    const character = text[index];
    if (blockDepth > 0) {
      if (text.startsWith("(*", index)) {
        blockDepth += 1;
        index += 1;
      } else if (text.startsWith("*)", index)) {
        blockDepth -= 1;
        index += 1;
      }
      continue;
    }
    if (lineComment) {
      if (character === "\n") lineComment = false;
      continue;
    }
    if (text.startsWith("(*", index)) {
      blockDepth = 1;
      index += 1;
    } else if (character === "#") {
      lineComment = true;
    } else if (character === ".") {
      const end = index + 1;
      const command = text.slice(statementStart, end);
      checkpoints.push({
        start: statementStart,
        end,
        range: currentLineRange(text, statementStart, end),
        label: commandLabel(command)
      });
      statementStart = end;
      if (isQedCommand(command)) break;
    }
  }
  return checkpoints;
}

function commandLabel(command) {
  return command
    .replace(/#[^\n]*/g, "")
    .replace(/\(\*[\s\S]*?\*\)/g, "")
    .trim()
    .replace(/\s+/g, " ");
}

function isQedCommand(command) {
  return commandLabel(command).toLowerCase() === "qed.";
}

function stepIndicatorText(index, checkpoint) {
  const total = interactiveCheckpoints.length;
  const lines = checkpoint.range.start === checkpoint.range.end
    ? (isJapanese ? `${checkpoint.range.start} 行目` : `line ${checkpoint.range.start}`)
    : (isJapanese
      ? `${checkpoint.range.start}–${checkpoint.range.end} 行目`
      : `lines ${checkpoint.range.start}–${checkpoint.range.end}`);
  return isJapanese
    ? `ステップ ${index + 1}/${total} · ${lines}`
    : `Step ${index + 1}/${total} · ${lines}`;
}

function updateNavigationControls() {
  previousStepButton.disabled = interactiveBusy || interactiveCursor <= 0;
  nextStepButton.disabled = interactiveBusy || interactiveCheckpoints.length === 0 ||
    interactiveCursor >= interactiveCheckpoints.length - 1;
}

function showInteractiveCursor(index) {
  const checkpoint = interactiveCheckpoints[index];
  interactiveRange = checkpoint.range;
  stepIndicator.textContent = stepIndicatorText(index, checkpoint);
  stepIndicator.title = checkpoint.label;
  updateLineNumbers();
}

async function moveInteractive(direction) {
  if (interactiveBusy) return;

  interactiveCheckpoints = proofCheckpoints(editor.value);
  if (interactiveCheckpoints.length === 0) {
    interactiveCursor = -1;
    interactiveRange = undefined;
    stepIndicator.textContent = ui.noTheorem;
    updateLineNumbers();
    updateNavigationControls();
    renderInteractive({
      ok: false,
      line: 1,
      message: ui.noTheoremFound
    });
    return;
  }

  const target = interactiveCursor < 0
    ? (direction > 0 ? 0 : -1)
    : interactiveCursor + direction;
  if (target < 0 || target >= interactiveCheckpoints.length) return;

  interactiveCursor = target;
  const checkpoint = interactiveCheckpoints[target];
  showInteractiveCursor(target);
  interactiveBusy = true;
  updateNavigationControls();
  try {
    const data = await inspectInteractive(editor.value.slice(0, checkpoint.end));
    renderInteractive(data);
  } catch (error) {
    renderInteractive({ ok: false, line: checkpoint.range.end, message: error.message });
  } finally {
    interactiveBusy = false;
    updateNavigationControls();
  }
}

async function loadAxioms() {
  const list = document.querySelector("#axiom-list");
  try {
    const api = await wasmApi();
    const axioms = JSON.parse(api.axioms);
    list.innerHTML = axioms.map((axiom, index) => `
      <article class="axiom">
        <span class="axiom-index">${String(index + 1).padStart(2, "0")}</span>
        <h3>${escapeHtml(axiom.key)}${axiom.key === "separation" || axiom.key === "replacement" ? ` <span class="axiom-kind">${ui.selectedScheme}</span>` : ""}</h3>
        <div class="axiom-formula">${escapeHtml(axiom.statement)}</div>
        <p>${escapeHtml(isJapanese ? (axiomNotesJa[axiom.key] || axiom.note) : axiom.note)}</p>
      </article>`).join("");
  } catch {
    list.innerHTML = `<div class="loading">Could not load the axiom library.</div>`;
  }
}

if (editor) {
  editor.addEventListener("input", () => {
    resetInteractive();
    if (tutorialInput) scheduleTutorialReset();
  });
  editor.addEventListener("scroll", () => {
    numbers.scrollTop = editor.scrollTop;
    updateEditorMarker();
  });
  editor.addEventListener("keydown", (event) => {
    if ((event.metaKey || event.ctrlKey) && event.key === "Enter") {
      event.preventDefault();
      verify();
    }
    if (event.key === "Tab") {
      event.preventDefault();
      const start = editor.selectionStart;
      editor.setRangeText("  ", start, editor.selectionEnd, "end");
      updateLineNumbers();
    }
  });
  verifyButton.addEventListener("click", verify);
  previousStepButton.addEventListener("click", () => moveInteractive(-1));
  nextStepButton.addEventListener("click", () => moveInteractive(1));
  exampleSelect.addEventListener("change", (event) => {
    setExample(event.target.value);
    if (tutorialInput) resetTutorial();
  });

  setExample("identity");
  loadAxioms();
}

if (tutorialInput) {
  tutorialApplyButton.addEventListener("click", applyTutorialTactic);
  tutorialInput.addEventListener("keydown", (event) => {
    if (event.key === "Enter") {
      event.preventDefault();
      applyTutorialTactic();
    }
  });
  tutorialResetButton.addEventListener("click", resetTutorial);
  tutorialExampleSelect?.addEventListener("change", resetTutorial);
  resetTutorial();
}
