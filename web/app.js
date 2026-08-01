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
exact Hempty.
qed.`,
  skolem: `Skolem pair Hpair from pairing.
theorem pair_shape :
  forall a, forall b, forall x,
    (x in pair(a,b) <-> (x = a or x = b)).
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
const interactiveButton = document.querySelector("#interactive-button");
const exampleSelect = document.querySelector("#example-select");
const goalView = document.querySelector("#goal-view");
const goalCount = document.querySelector("#goal-count");
const tacticInput = document.querySelector("#tactic-input");
const stepButton = document.querySelector("#step-button");
let interactiveActive = false;

function updateLineNumbers() {
  const count = editor.value.split("\n").length;
  numbers.textContent = Array.from({ length: count }, (_, i) => i + 1).join("\n");
  numbers.scrollTop = editor.scrollTop;
}

function setExample(name) {
  editor.value = examples[name];
  updateLineNumbers();
  interactiveActive = false;
  goalCount.textContent = "Not started";
  goalView.innerHTML = `<p>Select “Start interactive” to begin at the theorem declaration.</p>`;
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

async function verify() {
  verifyButton.disabled = true;
  verifyButton.querySelector("span").textContent = "Checking…";
  try {
    const response = await fetch("/api/check", {
      method: "POST",
      headers: { "Content-Type": "text/plain; charset=utf-8" },
      body: editor.value
    });
    const data = await response.json();
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
    goalView.innerHTML = declarationsHtml(data);
    result.className = "result success";
    result.innerHTML = `
      <div class="result-icon">✓</div>
      <p class="result-kicker">DECLARATIONS LOADED</p>
      <p>${escapeHtml(data.message)}</p>`;
    return;
  }

  if (data.qed) {
    goalCount.textContent = "Proof complete";
    goalView.innerHTML = `<span class="goal-target">✓ ${escapeHtml(data.statement)}</span>`;
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
      <p>Run <code>qed.</code> to finish the proof.</p>`;
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
    <span class="goal-target">⊢ ${escapeHtml(goal.target)}</span>`;
}

async function inspectInteractive() {
  const response = await fetch("/api/step", {
    method: "POST",
    headers: { "Content-Type": "text/plain; charset=utf-8" },
    body: editor.value
  });
  return response.json();
}

function prefixThroughTheorem(text) {
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
        return text.slice(0, index + 1);
      }
      statement = "";
    } else {
      statement += character === "\n" ? " " : character;
    }
  }
  return undefined;
}

async function startInteractive() {
  const prefix = prefixThroughTheorem(editor.value);
  if (!prefix) {
    renderInteractive({
      ok: false,
      line: 1,
      message: "No complete theorem declaration was found."
    });
    return false;
  }

  editor.value = prefix;
  updateLineNumbers();
  interactiveActive = true;
  interactiveButton.disabled = true;
  interactiveButton.querySelector("span").textContent = "Starting…";
  try {
    const data = await inspectInteractive();
    renderInteractive(data);
    tacticInput.focus();
    return data.ok;
  } catch (error) {
    renderInteractive({ ok: false, line: 1, message: error.message });
    return false;
  } finally {
    interactiveButton.disabled = false;
    interactiveButton.querySelector("span").textContent = "Restart interactive";
  }
}

async function runStep(tactic = tacticInput.value.trim()) {
  if (!tactic) return;
  if (!interactiveActive) {
    const started = await startInteractive();
    if (!started) return;
  }

  const before = editor.value;
  editor.value = `${before}\n${tactic}`;
  updateLineNumbers();
  stepButton.disabled = true;
  try {
    const data = await inspectInteractive();
    if (!data.ok) {
      editor.value = before;
      updateLineNumbers();
    } else {
      tacticInput.value = "";
    }
    renderInteractive(data);
  } catch (error) {
    editor.value = before;
    updateLineNumbers();
    renderInteractive({ ok: false, line: 1, message: error.message });
  } finally {
    stepButton.disabled = false;
    tacticInput.focus();
  }
}

async function loadAxioms() {
  const list = document.querySelector("#axiom-list");
  try {
    const response = await fetch("/api/axioms");
    const axioms = await response.json();
    list.innerHTML = axioms.map((axiom, index) => `
      <article class="axiom">
        <span class="axiom-index">${String(index + 1).padStart(2, "0")}</span>
        <h3>${escapeHtml(axiom.title)}</h3>
        <div class="axiom-formula">${escapeHtml(axiom.statement)}</div>
        <p>${escapeHtml(axiom.note)}</p>
        <span class="axiom-badge">${axiom.kernel ? "KERNEL AXIOM" : "SCHEMA"}</span>
      </article>`).join("");
  } catch {
    list.innerHTML = `<div class="loading">Could not load the axiom library.</div>`;
  }
}

editor.addEventListener("input", updateLineNumbers);
editor.addEventListener("scroll", () => { numbers.scrollTop = editor.scrollTop; });
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
interactiveButton.addEventListener("click", startInteractive);
stepButton.addEventListener("click", () => runStep());
tacticInput.addEventListener("keydown", (event) => {
  if (event.key === "Enter") {
    event.preventDefault();
    runStep();
  }
});
document.querySelectorAll("[data-tactic]").forEach((button) => {
  button.addEventListener("click", () => runStep(button.dataset.tactic));
});
exampleSelect.addEventListener("change", (event) => setExample(event.target.value));

setExample("identity");
loadAxioms();
