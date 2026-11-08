"use strict";

const assert = require("assert");
const http = require("http");
const path = require("path");
const {
  KernelClient,
  findProjectRoot,
  normalizeServerUrl,
  textThroughLine
} = require("../kernelClient");

assert.strictEqual(
  normalizeServerUrl("http://127.0.0.1:8099/"),
  "http://127.0.0.1:8099"
);
assert.strictEqual(textThroughLine("a\nb\nc", 0), "a");
assert.strictEqual(textThroughLine("a\nb\nc", 1), "a\nb");
assert.strictEqual(textThroughLine("a\nb\nc", 99), "a\nb\nc");
assert.throws(() => normalizeServerUrl("file:///tmp/kernel"));
assert.strictEqual(
  findProjectRoot(path.join(__dirname, "..", "..", "examples", "specialize.zfp")),
  path.resolve(__dirname, "..", "..")
);

async function testFilenameHeader() {
  const requests = [];
  const server = http.createServer((request, response) => {
    const chunks = [];
    request.on("data", (chunk) => chunks.push(chunk));
    request.on("end", () => {
      requests.push({
        endpoint: request.url,
        filename: request.headers["x-zfcert-filename"],
        body: Buffer.concat(chunks).toString("utf8")
      });
      response.end(JSON.stringify({ ok: true }));
    });
  });
  await new Promise((resolve, reject) => {
    server.once("error", reject);
    server.listen(0, "127.0.0.1", resolve);
  });
  try {
    const client = new KernelClient(`http://127.0.0.1:${server.address().port}`);
    const filename = path.resolve("証明 #100%", "main.zfp");
    const script = 'input "基本.zfp".\n';
    await client.step(script, filename);
    await client.check(script, filename);
    await client.check(script);
    await client.health();
    assert.deepStrictEqual(requests, [
      { endpoint: "/api/step", filename: encodeURIComponent(filename), body: script },
      { endpoint: "/api/check", filename: encodeURIComponent(filename), body: script },
      { endpoint: "/api/check", filename: undefined, body: script },
      { endpoint: "/api/health", filename: undefined, body: "" }
    ]);
  } finally {
    await new Promise((resolve) => server.close(resolve));
  }
}

testFilenameHeader().then(() => {
  console.log("kernelClient tests passed");
}).catch((error) => {
  console.error(error);
  process.exitCode = 1;
});
