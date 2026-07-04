"use strict";

const assert = require("assert");
const fs = require("fs");
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

  const definitionsProof = fs.readFileSync(
    path.join(__dirname, "..", "..", "examples", "definitions.zfp"),
    "utf8"
  );
  const definitionLines = definitionsProof.split(/\r?\n/);
  const firstDefinitionEnd = definitionLines.findIndex((line) =>
    line.includes("not (y in x)."));
  const definitionsOnly = await client.step(
    textThroughLine(definitionsProof, firstDefinitionEnd)
  );
  assert.strictEqual(definitionsOnly.ok, true);
  assert.strictEqual(definitionsOnly.definitionsOnly, true);
  assert.strictEqual(definitionsOnly.definitions[0].name, "is_empty");
  assert.deepStrictEqual(definitionsOnly.definitions[0].parameters, ["x"]);

  const definedTheorem = await client.check(definitionsProof);
  assert.strictEqual(definedTheorem.ok, true);
  assert.strictEqual(definedTheorem.theorem, "definition_identity");
  assert.strictEqual(definedTheorem.definitions.length, 2);

  const rulesProof = fs.readFileSync(
    path.join(__dirname, "..", "..", "examples", "rules.zfp"),
    "utf8"
  );
  const ruleResult = await client.check(rulesProof);
  assert.strictEqual(ruleResult.ok, true);
  assert.strictEqual(ruleResult.theorem, "equality_transport_by_rules");

  console.log("VS Code client integration tests passed");
}

main().catch((error) => {
  console.error(error);
  process.exitCode = 1;
});
