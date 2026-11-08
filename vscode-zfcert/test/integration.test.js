"use strict";

const assert = require("assert");
const fs = require("fs");
const os = require("os");
const path = require("path");
const { KernelClient, textThroughLine } = require("../kernelClient");

async function main() {
  const proof = fs.readFileSync(
    path.join(__dirname, "..", "..", "examples", "specialize.zfp"),
    "utf8"
  );
  const client = new KernelClient(
    process.env.ZFCERT_SERVER_URL || "http://127.0.0.1:8099"
  );

  const proofLines = proof.split(/\r?\n/);
  const theoremEnd = proofLines.findIndex((line) =>
    line.includes("a in b -> b in a))."));
  const specializeLine = proofLines.findIndex((line) =>
    line.trim().startsWith("specialize "));

  const initial = await client.step(textThroughLine(proof, theoremEnd));
  assert.strictEqual(initial.ok, true);
  assert.strictEqual(initial.goals.length, 1);
  assert.match(initial.goals[0].target, /^∀a,/);

  const specialized = await client.step(textThroughLine(proof, specializeLine));
  assert.strictEqual(specialized.ok, true);
  assert.strictEqual(
    specialized.goals[0].context.some((entry) =>
      entry.name === "Hna" && entry.formula === "¬a ∈ b"
    ),
    true
  );

  const complete = await client.check(proof);
  assert.strictEqual(complete.ok, true);
  assert.strictEqual(complete.theorem, "universal_contradiction");
  assert.strictEqual(
    complete.message,
    "The proof was verified by the extracted kernel."
  );

  const rejected = await client.check("bogus.");
  assert.strictEqual(rejected.ok, false);
  assert.strictEqual(
    rejected.message,
    "After aliases and choose declarations, use: theorem name : formula."
  );

  const commented = await client.check(`(* A block comment may contain periods.
    It may also contain (* nested comments *). *)
    theorem commented_identity : forall x, x = x.
    intro (* the introduced variable *) x.
    refl. # Legacy line comments remain supported.
    qed.`);
  assert.strictEqual(commented.ok, true);
  assert.strictEqual(commented.theorem, "commented_identity");

  const unterminatedComment = await client.check("(* never closed");
  assert.strictEqual(unterminatedComment.ok, false);
  assert.strictEqual(unterminatedComment.message, "Unterminated block comment.");

  const aliasesProof = fs.readFileSync(
    path.join(__dirname, "..", "..", "examples", "aliases.zfp"),
    "utf8"
  );
  const aliasLines = aliasesProof.split(/\r?\n/);
  const firstAliasEnd = aliasLines.findIndex((line) =>
    line.includes("not (y in x)."));
  const aliasesOnly = await client.step(
    textThroughLine(aliasesProof, firstAliasEnd)
  );
  assert.strictEqual(aliasesOnly.ok, true);
  assert.strictEqual(aliasesOnly.aliasesOnly, true);
  assert.strictEqual(aliasesOnly.aliases[0].name, "is_empty");
  assert.deepStrictEqual(aliasesOnly.aliases[0].parameters, ["x"]);

  const aliasedTheorem = await client.check(aliasesProof);
  assert.strictEqual(aliasedTheorem.ok, true);
  assert.strictEqual(aliasedTheorem.theorem, "alias_identity");
  assert.strictEqual(aliasedTheorem.aliases.length, 2);

  const obtainResult = await client.check(`theorem obtain_witness :
    (exists x, x = x) -> exists y, y = y.
  intro H.
  obtain x Hx from H.
  use x.
  exact Hx.
  qed.`);
  assert.strictEqual(obtainResult.ok, true);

  const chooseProof = fs.readFileSync(
    path.join(__dirname, "..", "..", "examples", "choose.zfp"),
    "utf8"
  );
  const chooseLine = chooseProof.split(/\r?\n/).findIndex((line) =>
    line.trim().startsWith("choose ")
  );
  const chooseDeclaration = await client.step(
    textThroughLine(chooseProof, chooseLine)
  );
  assert.strictEqual(chooseDeclaration.ok, true);
  assert.strictEqual(chooseDeclaration.aliasesOnly, true);
  assert.strictEqual(chooseDeclaration.steps, 1);

  const chooseResult = await client.check(`alias is_empty x :=
    forall y, not (y in x).
  choose empty Hempty from empty_set.
  theorem chosen_empty : is_empty empty.
  exact Hempty.
  qed.`);
  assert.strictEqual(chooseResult.ok, true);

  const rulesProof = fs.readFileSync(
    path.join(__dirname, "..", "..", "examples", "rules.zfp"),
    "utf8"
  );
  const ruleResult = await client.check(rulesProof);
  assert.strictEqual(ruleResult.ok, true);
  assert.strictEqual(ruleResult.theorem, "equality_transport_by_rules");

  const directory = fs.mkdtempSync(path.join(os.tmpdir(), "zfcert input 証明 #100%-"));
  try {
    fs.mkdirSync(path.join(directory, "lib"));
    fs.writeFileSync(path.join(directory, "lib", "base.zfp"), `
      theorem imported_identity : forall x, x = x.
      intro x.
      refl.
      qed.`);
    fs.writeFileSync(path.join(directory, "lib", "middle.zfp"), 'input "base.zfp".');
    const filename = path.join(directory, "main.zfp");
    // The editor buffer is authoritative even when the root file differs on disk.
    fs.writeFileSync(filename, "bogus.");
    const script = `input "lib/middle.zfp".
      theorem from_input : forall x, x = x.
      put imported_identity.
      exact imported_identity.
      qed.`;
    const included = await client.check(script, filename);
    assert.strictEqual(included.ok, true, included.message);
    assert.strictEqual(included.theorem, "from_input");

    const afterInput = await client.step(textThroughLine(script, 2), filename);
    assert.strictEqual(afterInput.ok, true, afterInput.message);
    assert.strictEqual(afterInput.goals[0].context.some((entry) =>
      entry.name === "imported_identity"), true);

    fs.writeFileSync(path.join(directory, "lib", "base.zfp"), "\nbogus.");
    const invalidInput = await client.check(script, filename);
    assert.strictEqual(invalidInput.ok, false);
    assert.strictEqual(invalidInput.line, 1);
    assert.ok(invalidInput.message.includes("base.zfp:2"), invalidInput.message);
  } finally {
    fs.rmSync(directory, { recursive: true, force: true });
  }

  console.log("VS Code client integration tests passed");
}

main().catch((error) => {
  console.error(error);
  process.exitCode = 1;
});
