"use strict";

const vscode = require("vscode");
const childProcess = require("child_process");
const fs = require("fs");
const path = require("path");
const { KernelClient, findProjectRoot, textThroughLine } = require("./kernelClient");

let kernelProcess;
let kernelStarting;
let analysisTimer;
let lastAnalysisVersion = -1;

function escapeHtml(value) {
  return String(value)
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;");
}

class GoalViewProvider {
  constructor() {
    this.view = undefined;
    this.data = undefined;
  }

  resolveWebviewView(view) {
    this.view = view;
    view.webview.options = { enableScripts: false };
    this.render();
  }

  update(data) {
    this.data = data;
    this.render();
  }

  render() {
    if (!this.view) return;
    this.view.webview.html = this.html(this.data);
  }

  html(data) {
    const style = `
      body { padding: 12px 14px; color: var(--vscode-foreground);
             font-family: var(--vscode-font-family); }
      .muted { color: var(--vscode-descriptionForeground); line-height: 1.5; }
      .status { font-size: 11px; letter-spacing: .08em; text-transform: uppercase;
                color: var(--vscode-descriptionForeground); margin-bottom: 14px; }
      .error { border-left: 3px solid var(--vscode-errorForeground);
               padding: 9px 11px; background: var(--vscode-inputValidation-errorBackground); }
      .success { border-left: 3px solid var(--vscode-testing-iconPassed);
                 padding: 9px 11px; }
      .goal { border: 1px solid var(--vscode-panel-border); margin: 0 0 14px; }
      .goal-number { padding: 7px 10px; font-size: 11px;
                     color: var(--vscode-descriptionForeground);
                     border-bottom: 1px solid var(--vscode-panel-border); }
      .context { padding: 9px 10px; border-bottom: 1px solid var(--vscode-panel-border); }
      .context-row { margin: 4px 0; font-family: var(--vscode-editor-font-family); }
      .name { color: var(--vscode-symbolIcon-variableForeground); font-weight: 600; }
      .target { padding: 12px 10px; font-family: var(--vscode-editor-font-family);
                color: var(--vscode-symbolIcon-functionForeground); overflow-wrap: anywhere; }
      code { font-family: var(--vscode-editor-font-family); }
    `;

    let content;
    if (!data) {
      content = `<p class="muted">Open a <code>.zfp</code> file and place the cursor after a tactic.</p>`;
    } else if (!data.ok) {
      content = `
        <div class="status">Rejected · line ${data.line || "?"}</div>
        <div class="error">${escapeHtml(data.message)}</div>`;
    } else if (data.definitionsOnly) {
      const definitions = (data.definitions || []).map((definition) => `
        <div class="context-row"><span class="name">${escapeHtml(
          [definition.name, ...(definition.parameters || [])].join(" ")
        )}</span> := ${escapeHtml(definition.statement)}</div>`).join("");
      content = `
        <div class="status">${(data.definitions || []).length} definitions</div>
        <div class="success">✓ ${escapeHtml(data.message)}</div>
        <div class="context">${definitions}</div>`;
    } else if (data.qed || !Array.isArray(data.goals)) {
      content = `
        <div class="status">Verified · ${data.steps} steps</div>
        <div class="success">✓ ${escapeHtml(data.theorem)}<br>
          <span class="muted">${escapeHtml(data.statement)}</span>
        </div>`;
    } else if (data.complete) {
      content = `
        <div class="status">0 goals</div>
        <div class="success">All goals solved. Add <code>qed</code> to finish.</div>`;
    } else {
      const goals = data.goals.map((goal, index) => {
        const context = goal.context.length === 0
          ? `<div class="muted">No assumptions</div>`
          : goal.context.map((entry) => `
              <div class="context-row"><span class="name">${escapeHtml(entry.name)}</span>
              : ${escapeHtml(entry.formula)}</div>`).join("");
        return `
          <section class="goal">
            <div class="goal-number">GOAL ${index + 1} / ${data.goals.length}</div>
            <div class="context">${context}</div>
            <div class="target">⊢ ${escapeHtml(goal.target)}</div>
          </section>`;
      }).join("");
      content = `<div class="status">${data.steps} steps · ${data.goals.length} goals</div>${goals}`;
    }

    return `<!doctype html><html><head><meta charset="utf-8">
      <meta http-equiv="Content-Security-Policy" content="default-src 'none'; style-src 'unsafe-inline';">
      <style>${style}</style></head><body>${content}</body></html>`;
  }
}

function configuration() {
  return vscode.workspace.getConfiguration("zfcert");
}

function activeProofEditor() {
  const editor = vscode.window.activeTextEditor;
  if (!editor || editor.document.languageId !== "zfcert") return undefined;
  return editor;
}

function workspaceRoot(editor) {
  const configured = configuration().get("workspaceRoot", "").trim();
  if (configured) return configured;

  const candidates = [];
  if (editor?.document.uri.scheme === "file") {
    candidates.push(editor.document.uri.fsPath);
  }
  const containingFolder = editor
    ? vscode.workspace.getWorkspaceFolder(editor.document.uri)
    : undefined;
  if (containingFolder) candidates.push(containingFolder.uri.fsPath);
  for (const folder of vscode.workspace.workspaceFolders || []) {
    candidates.push(folder.uri.fsPath);
  }

  for (const candidate of candidates) {
    const found = findProjectRoot(candidate);
    if (found) return found;
  }
  return undefined;
}

function client() {
  return new KernelClient(configuration().get("serverUrl"));
}

function kernelPort() {
  const url = new URL(configuration().get("serverUrl"));
  if (url.port) return Number(url.port);
  return url.protocol === "https:" ? 443 : 80;
}

async function waitForKernel(output) {
  const kernel = client();
  for (let attempt = 0; attempt < 40; attempt += 1) {
    try {
      const health = await kernel.health();
      if (health.service === "zfcert") return;
    } catch {
      await new Promise((resolve) => setTimeout(resolve, 100));
    }
  }
  output.show(true);
  throw new Error("The OCaml kernel did not become ready");
}

async function ensureKernel(editor, output, status) {
  try {
    const health = await client().health();
    if (health.service === "zfcert") {
      status.text = "$(check) ZFCert kernel";
      return;
    }
  } catch {
    // Fall through to optional local startup.
  }
  if (!configuration().get("autoStartKernel")) {
    throw new Error("ZFCert kernel is not reachable. Run “ZFCert: Restart Kernel”.");
  }

  if (kernelStarting) return kernelStarting;
  kernelStarting = (async () => {
    const root = workspaceRoot(editor);
    if (!root || !fs.existsSync(path.join(root, "dune-project"))) {
      throw new Error("Cannot find dune-project. Set zfcert.workspaceRoot.");
    }

    if (kernelProcess && !kernelProcess.killed) kernelProcess.kill();
    const server = new URL(configuration().get("serverUrl"));
    if (!["127.0.0.1", "localhost", "::1"].includes(server.hostname)) {
      throw new Error("Automatic kernel startup is only available for localhost URLs.");
    }
    const dune = configuration().get("dunePath");
    const args = ["exec", "src/main.exe", "--", "--port", String(kernelPort())];
    output.appendLine(`Starting kernel in ${root}`);
    const processHandle = childProcess.spawn(dune, args, {
      cwd: root,
      env: process.env,
      stdio: ["ignore", "pipe", "pipe"]
    });
    kernelProcess = processHandle;
    processHandle.stdout.on("data", (chunk) => output.append(chunk.toString()));
    processHandle.stderr.on("data", (chunk) => output.append(chunk.toString()));
    processHandle.on("error", (error) => output.appendLine(error.message));
    processHandle.on("exit", (code, signal) => {
      output.appendLine(`Kernel stopped (${signal || code})`);
      if (kernelProcess === processHandle) {
        status.text = "$(circle-slash) ZFCert kernel";
        kernelProcess = undefined;
      }
    });
    await waitForKernel(output);
    status.text = "$(check) ZFCert kernel";
  })();

  try {
    await kernelStarting;
  } finally {
    kernelStarting = undefined;
  }
}

function stopKernelProcess() {
  const processHandle = kernelProcess;
  kernelProcess = undefined;
  if (!processHandle || processHandle.killed) return Promise.resolve();
  return new Promise((resolve) => {
    const timer = setTimeout(resolve, 1500);
    processHandle.once("exit", () => {
      clearTimeout(timer);
      resolve();
    });
    processHandle.kill();
  });
}

function diagnosticFor(document, data) {
  if (data.ok) return [];
  const line = Math.max(0, Math.min((data.line || 1) - 1, document.lineCount - 1));
  const range = document.lineAt(line).range;
  const diagnostic = new vscode.Diagnostic(
    range,
    data.message,
    vscode.DiagnosticSeverity.Error
  );
  diagnostic.source = "ZFCert kernel";
  return [diagnostic];
}

async function analyze(editor, line, services, force = false) {
  if (!editor) return;
  const document = editor.document;
  if (!force && lastAnalysisVersion === document.version && line === editor.selection.active.line) {
    return;
  }

  await ensureKernel(editor, services.output, services.status);
  const script = textThroughLine(document.getText(), line);
  const data = await client().step(script);
  lastAnalysisVersion = document.version;
  services.goals.update(data);
  services.diagnostics.set(document.uri, diagnosticFor(document, data));
  if (data.ok) {
    services.status.text = data.definitionsOnly
      ? `$(symbol-constant) ${data.definitions.length} definitions`
      : data.qed
      ? `$(pass) ${data.theorem}`
      : `$(target) ${data.goals.length} goal${data.goals.length === 1 ? "" : "s"}`;
  } else {
    services.status.text = `$(error) line ${data.line}`;
  }
  return data;
}

function reportError(error, services) {
  const message = error instanceof Error ? error.message : String(error);
  services.output.appendLine(message);
  services.status.text = "$(error) ZFCert kernel";
  if (message.includes("Cannot find dune-project")) {
    vscode.window.showErrorMessage(
      `ZFCert: ${message}`,
      "Select Project Folder"
    ).then((choice) => {
      if (choice === "Select Project Folder") {
        vscode.commands.executeCommand("zfcert.selectWorkspaceRoot");
      }
    });
  } else {
    vscode.window.showErrorMessage(`ZFCert: ${message}`);
  }
}

function scheduleAnalysis(editor, services) {
  if (!configuration().get("analyzeOnType") || !editor) return;
  clearTimeout(analysisTimer);
  analysisTimer = setTimeout(() => {
    analyze(editor, editor.selection.active.line, services, true)
      .catch((error) => reportError(error, services));
  }, 250);
}

function tacticCompletions() {
  const entries = [
    ["Definition", "Definition ${1:is_empty} ${2:x} := ${3:forall y, not (y in x)}.", "Give a transparent name to a proposition, optionally with arguments"],
    ["rule", "rule ${1|axiom,hypothesis,falsum_elim,impl_intro,impl_elim,conj_intro,conj_elim_l,conj_elim_r,disj_intro_l,disj_intro_r,disj_elim,all_intro,all_elim,ex_intro,ex_elim,equal_refl,equal_elim,cut|}.", "Apply one primitive natural-deduction rule"],
    ["rule cut", "rule cut ${1:H} : ${2:P}.", "Introduce and prove an intermediate proposition with Cut"],
    ["rule equal_elim", "rule equal_elim ${1:s} ${2:t} ${3:x} : ${4:P}.", "Apply primitive equality elimination"],
    ["intro", "intro ${1:H}.", "Introduce an implication, negation, or universal variable"],
    ["exact", "exact ${1:H}.", "Close the goal with a matching fact"],
    ["apply", "apply ${1:H}.", "Apply a fact backwards"],
    ["specialize", "specialize ${1:H} ${2:a} as ${3:H_a}.", "Instantiate a universal fact"],
    ["cases", "cases ${1:H} ${2:H1} ${3:H2}.", "Eliminate conjunction, equivalence, or existence"],
    ["use", "use ${1:x}.", "Provide an existential witness"],
    ["refl", "refl.", "Prove reflexive equality"],
    ["split", "split.", "Split conjunction or equivalence"],
    ["assumption", "assumption.", "Use a matching assumption"],
    ["contradiction", "contradiction.", "Close a goal from contradictory assumptions"],
    ["left", "left.", "Choose the left disjunct"],
    ["right", "right.", "Choose the right disjunct"],
    ["qed", "qed.", "Finish a solved proof"],
    ["empty_set", "exact empty_set.", "Use the empty-set axiom"],
    ["extensionality", "apply extensionality.", "Apply extensionality"]
  ];
  return entries.map(([label, insert, detail]) => {
    const item = new vscode.CompletionItem(label, vscode.CompletionItemKind.Keyword);
    item.insertText = new vscode.SnippetString(insert);
    item.detail = detail;
    return item;
  });
}

function activate(context) {
  const output = vscode.window.createOutputChannel("ZFCert");
  const diagnostics = vscode.languages.createDiagnosticCollection("zfcert");
  const goals = new GoalViewProvider();
  const status = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 50);
  status.name = "ZFCert";
  status.text = "$(circle-outline) ZFCert kernel";
  status.command = "zfcert.runToCursor";
  status.show();
  const services = { output, diagnostics, goals, status };

  context.subscriptions.push(
    output,
    diagnostics,
    status,
    vscode.window.registerWebviewViewProvider("zfcert.goals", goals),
    vscode.languages.registerCompletionItemProvider("zfcert", {
      provideCompletionItems: tacticCompletions
    }),
    vscode.commands.registerCommand("zfcert.runToCursor", async () => {
      const editor = activeProofEditor();
      if (!editor) return vscode.window.showInformationMessage("Open a .zfp proof file first.");
      try {
        await analyze(editor, editor.selection.active.line, services, true);
      } catch (error) {
        reportError(error, services);
      }
    }),
    vscode.commands.registerCommand("zfcert.checkProof", async () => {
      const editor = activeProofEditor();
      if (!editor) return vscode.window.showInformationMessage("Open a .zfp proof file first.");
      try {
        await ensureKernel(editor, output, status);
        const data = await client().check(editor.document.getText());
        goals.update(data);
        diagnostics.set(editor.document.uri, diagnosticFor(editor.document, data));
        if (data.ok) {
          if (data.definitionsOnly) {
            status.text = `$(symbol-constant) ${data.definitions.length} definitions`;
            vscode.window.showInformationMessage(`Loaded ${data.definitions.length} proposition definitions`);
          } else {
            status.text = `$(pass) ${data.theorem}`;
            vscode.window.showInformationMessage(`Verified ${data.theorem} (${data.steps} steps)`);
          }
        } else {
          status.text = `$(error) line ${data.line}`;
        }
      } catch (error) {
        reportError(error, services);
      }
    }),
    vscode.commands.registerCommand("zfcert.restartKernel", async () => {
      try {
        await stopKernelProcess();
        await ensureKernel(activeProofEditor(), output, status);
        vscode.window.showInformationMessage("ZFCert kernel restarted.");
      } catch (error) {
        reportError(error, services);
      }
    }),
    vscode.commands.registerCommand("zfcert.stopKernel", async () => {
      await stopKernelProcess();
      status.text = "$(circle-slash) ZFCert kernel";
    }),
    vscode.commands.registerCommand("zfcert.selectWorkspaceRoot", async () => {
      const selected = await vscode.window.showOpenDialog({
        canSelectFiles: false,
        canSelectFolders: true,
        canSelectMany: false,
        openLabel: "Use as ZFCert Project"
      });
      if (!selected?.[0]) return;
      const root = findProjectRoot(selected[0].fsPath);
      if (!root) {
        vscode.window.showErrorMessage("The selected folder does not contain dune-project.");
        return;
      }
      await configuration().update(
        "workspaceRoot",
        root,
        vscode.ConfigurationTarget.Global
      );
      try {
        await stopKernelProcess();
        await ensureKernel(activeProofEditor(), output, status);
        vscode.window.showInformationMessage(`ZFCert project: ${root}`);
      } catch (error) {
        reportError(error, services);
      }
    }),
    vscode.commands.registerCommand("zfcert.showGoals", async () => {
      await vscode.commands.executeCommand("workbench.view.extension.zfcert");
      await vscode.commands.executeCommand("zfcert.goals.focus");
      const editor = activeProofEditor();
      if (editor) {
        try {
          await analyze(editor, editor.selection.active.line, services, true);
        } catch (error) {
          reportError(error, services);
        }
      }
    }),
    vscode.workspace.onDidChangeTextDocument((event) => {
      const editor = activeProofEditor();
      if (editor && event.document === editor.document) scheduleAnalysis(editor, services);
    }),
    vscode.window.onDidChangeTextEditorSelection((event) => {
      if (event.textEditor.document.languageId === "zfcert") {
        scheduleAnalysis(event.textEditor, services);
      }
    }),
    vscode.window.onDidChangeActiveTextEditor((editor) => {
      if (editor?.document.languageId === "zfcert") scheduleAnalysis(editor, services);
    })
  );

  if (activeProofEditor()) {
    setTimeout(() => {
      vscode.commands.executeCommand("zfcert.showGoals");
    }, 100);
  }
  scheduleAnalysis(activeProofEditor(), services);
}

function deactivate() {
  clearTimeout(analysisTimer);
  void stopKernelProcess();
}

module.exports = { activate, deactivate };
