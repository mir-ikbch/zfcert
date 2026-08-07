const examples = {
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

const editor = document.querySelector("#proof-editor");
const numbers = document.querySelector("#line-numbers");
const result = document.querySelector("#result");
const verifyButton = document.querySelector("#verify-button");
const exampleSelect = document.querySelector("#example-select");
const goalView = document.querySelector("#goal-view");
const goalCount = document.querySelector("#goal-count");
const editorMarker = document.querySelector("#editor-marker");
const previousStepButton = document.querySelector("#previous-step-button");
const nextStepButton = document.querySelector("#next-step-button");
const stepIndicator = document.querySelector("#step-indicator");
let interactiveCursor = -1;
let interactiveCheckpoints = [];
let interactiveRange;
let interactiveBusy = false;
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
  goalCount.textContent = "Not started";
  stepIndicator.textContent = "Not started";
  goalView.innerHTML = `<p>Press ↓ to begin at the theorem declaration.</p>`;
  updateLineNumbers();
  updateNavigationControls();
}

function setExample(name) {
  editor.value = examples[name];
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
      <summary>Show checked primitive rules (${rules.length})</summary>
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
    `<code>${escapeHtml(name)}</code> (constant)`
  );
  const facts = (data.facts || []).map((fact) =>
    `<code>${escapeHtml(fact.name)}</code> : ${escapeHtml(fact.formula)}`
  );
  return [...aliases, ...constants, ...facts].join("<br>");
}

function declarationSummary(data) {
  return `${(data.aliases || []).length} aliases · ${(data.constants || []).length} constants`;
}

function currentCommandHtml() {
  const checkpoint = interactiveCheckpoints[interactiveCursor];
  if (!checkpoint) return "";
  return `<span class="step-command">Current: ${escapeHtml(checkpoint.label)}</span>`;
}

async function verify() {
  verifyButton.disabled = true;
  verifyButton.querySelector("span").textContent = "Checking…";
  try {
    const api = await wasmApi();
    const data = JSON.parse(api.check(editor.value));
    if (data.ok && data.aliasesOnly) {
      result.className = "result success";
      result.innerHTML = `
        <div class="result-icon">✓</div>
        <p class="result-kicker">${escapeHtml(declarationSummary(data))}</p>
        <h3>Global declarations loaded</h3>
        <p>${declarationsHtml(data)}</p>`;
    } else if (data.ok) {
      result.className = "result success";
      result.innerHTML = `
        <div class="result-icon">✓</div>
        <p class="result-kicker">VERIFIED · ${data.steps} STEPS</p>
        <h3>${escapeHtml(data.theorem)}</h3>
        <p><code>${escapeHtml(data.statement)}</code><br>${escapeHtml(data.message)}</p>
        ${certificateHtml(data.certificate)}`;
    } else {
      result.className = "result error";
      result.innerHTML = `
        <div class="result-icon">!</div>
        <p class="result-kicker">REJECTED · LINE ${data.line}</p>
        <h3>The proof could not be verified</h3>
        <p>${escapeHtml(data.message)}</p>`;
    }
  } catch (error) {
    result.className = "result error";
    result.innerHTML = `
      <div class="result-icon">!</div>
      <p class="result-kicker">CONNECTION ERROR</p>
      <h3>Cannot connect to the kernel</h3>
      <p>${escapeHtml(error.message)}</p>`;
  } finally {
    verifyButton.disabled = false;
    verifyButton.querySelector("span").textContent = "Verify proof";
  }
}

function renderInteractive(data) {
  if (!data.ok) {
    goalCount.textContent = "Step rejected";
    goalView.innerHTML = `<p>${escapeHtml(data.message)}</p>`;
    result.className = "result error";
    result.innerHTML = `
      <div class="result-icon">!</div>
      <p class="result-kicker">STEP REJECTED · LINE ${data.line}</p>
      <h3>The step was rejected</h3>
      <p>${escapeHtml(data.message)}</p>`;
    return;
  }

  if (data.aliasesOnly) {
    goalCount.textContent = declarationSummary(data);
    goalView.innerHTML = `${declarationsHtml(data)}${currentCommandHtml()}`;
    result.className = "result success";
    result.innerHTML = `
      <div class="result-icon">✓</div>
      <p class="result-kicker">DECLARATIONS LOADED</p>
      <p>${escapeHtml(data.message)}</p>`;
    return;
  }

  if (data.qed) {
    goalCount.textContent = "Proof complete";
    goalView.innerHTML = `
      <span class="goal-target">✓ ${escapeHtml(data.statement)}</span>
      ${currentCommandHtml()}`;
    result.className = "result success";
    result.innerHTML = `
      <div class="result-icon">✓</div>
      <p class="result-kicker">VERIFIED · ${data.steps} STEPS</p>
      <h3>${escapeHtml(data.theorem)}</h3>
      <p>${escapeHtml(data.message)}</p>
      ${certificateHtml(data.certificate)}`;
    return;
  }

  result.className = "result active";
  result.innerHTML = `
    <div class="result-icon">${data.complete ? "✓" : "→"}</div>
    <p class="result-kicker">${data.complete ? "GOALS SOLVED" : `INTERACTIVE · ${data.steps} STEPS`}</p>
    <h3>${escapeHtml(data.theorem)}</h3>
    <p>${escapeHtml(data.message)}</p>`;

  if (data.complete) {
    goalCount.textContent = "0 goals";
    goalView.innerHTML = `
      <span class="goal-target">All goals solved</span>
      <p>Run <code>qed.</code> to finish the proof.</p>
      ${currentCommandHtml()}`;
    return;
  }

  const goal = data.goals[0];
  goalCount.textContent = `${data.goals.length} goal${data.goals.length === 1 ? "" : "s"}`;
  const context = goal.context.length
    ? `<ul class="goal-context">${goal.context.map((entry) =>
        `<li><strong>${escapeHtml(entry.name)}</strong> : ${escapeHtml(entry.formula)}</li>`
      ).join("")}</ul>`
    : `<p class="goal-context">No assumptions</p>`;
  goalView.innerHTML = `
    ${context}
    <span class="goal-target">⊢ ${escapeHtml(goal.target)}</span>
    ${currentCommandHtml()}`;
}

async function inspectInteractive(script) {
  const api = await wasmApi();
  return JSON.parse(api.step(script));
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
    ? `line ${checkpoint.range.start}`
    : `lines ${checkpoint.range.start}–${checkpoint.range.end}`;
  return `Step ${index + 1}/${total} · ${lines}`;
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
    stepIndicator.textContent = "No theorem";
    updateLineNumbers();
    updateNavigationControls();
    renderInteractive({
      ok: false,
      line: 1,
      message: "No complete theorem declaration was found."
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
        <h3>${escapeHtml(axiom.key)}${axiom.key === "separation" || axiom.key === "replacement" ? ' <span class="axiom-kind">(scheme)</span>' : ""}</h3>
        <div class="axiom-formula">${escapeHtml(axiom.statement)}</div>
        <p>${escapeHtml(axiom.note)}</p>
      </article>`).join("");
  } catch {
    list.innerHTML = `<div class="loading">Could not load the axiom library.</div>`;
  }
}

editor.addEventListener("input", resetInteractive);
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
exampleSelect.addEventListener("change", (event) => setExample(event.target.value));

setExample("identity");
loadAxioms();
